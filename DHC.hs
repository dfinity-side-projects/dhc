{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PackageImports #-}
module DHC (parseContract, ExternType, AstF(..), Ast(..), AstPlus(..), Type(..), inferType, parseDefs, lexOffside,
  preludeMinimal, arityFromType, hsToAst, liftLambdas) where

import Control.Arrow
import Control.Monad
import Data.Binary (Binary)
#ifdef __HASTE__
import "mtl" Control.Monad.State
import Data.ByteString (ByteString, pack)
#else
import Control.Monad.State
import Data.ByteString.Short (ShortByteString, pack)
#endif
import Data.ByteString.Internal (c2w)
import Data.Char
import Data.Int
import Data.List
import qualified Data.Map.Strict as M
import Data.Map.Strict (Map)
import Data.Maybe
import GHC.Generics (Generic)
import Text.Parsec hiding (State)

#ifdef __HASTE__
type ShortByteString = ByteString
#endif

instance Binary Type

infixl 5 :@
data AstF a = Qual String String | CCall String String
  | Pack Int Int | I Int64 | S ShortByteString | Var String
  | a :@ a | Cas a [(a, a)]
  | Lam [String] a | Let [(String, a)] a
  | Placeholder String Type deriving (Read, Show, Functor, Generic)

newtype Ast = Ast (AstF Ast) deriving (Show, Generic)

-- Annotated AST.
data AAst a = AAst a (AstF (AAst a)) deriving (Show, Functor)

-- | Knowing the arity of functions from other contracts
-- can aid correctness checks during compilation.
type ExternType = String -> String -> Maybe Int

deAnn :: AAst a -> Ast
deAnn = ffix $ \h (AAst _ ast) -> Ast $ h ast

ffix :: Functor f => ((f a -> f b) -> a -> b) -> a -> b
ffix f = f $ fmap $ ffix f

infixr 5 :->
data Type = TC String | TApp Type Type | Type :-> Type
  | TV String | GV String deriving (Read, Show, Eq, Generic)

data LayoutState = IndentAgain Int | LineStart | LineMiddle | AwaitBrace | Boilerplate deriving (Eq, Show)
type Parser = Parsec String (LayoutState, [Int])

program :: Parser [(String, Ast)]
program = do
  filler
  defs <- supercombinators
  eof
  pure defs

data Associativity = LAssoc | RAssoc | NAssoc deriving (Eq, Show)

standardFixities :: Map String (Associativity, Int)
standardFixities = M.fromList $ concatMap (f . words)
  [ "infixl 9 !!"
  , "infixr 9 ."
  , "infixr 8 ^ ^^ **"
  , "infixl 7 * / div mod rem quot"
  , "infixl 6 + -"
  , "infixr 5 : ++"
  , "infix 4 == /= < <= > >= elem notElem"
  , "infixr 3 &&"
  , "infixr 2 ||"
  , "infixl 1 >> >>="
  , "infixr 0 $ $! seq"
  ]
  where
    f (assoc:prec:ops) = flip (,) (parseAssoc assoc, read prec) <$> ops
    f _ = undefined
    parseAssoc "infix"  = NAssoc
    parseAssoc "infixl" = LAssoc
    parseAssoc "infixr" = RAssoc
    parseAssoc _ = error "BUG! bad associativity"

fixity :: String -> (Associativity, Int)
fixity o = fromMaybe (LAssoc, 9) $ M.lookup o standardFixities

supercombinators :: Parser [(String, Ast)]
supercombinators = catMaybes <$> between (want "{") (want "}") (sc `sepBy` want ";") where
  sc = try (do
    (fun:args) <- scOp <|> many1 varStr
    void $ want "="
    Just . (,) fun . Ast . Lam args <$> expr) <|> pure Nothing
  scOp = try $ do
    l <- varStr
    op <- varSym
    r <- varStr
    pure [op, l, r]
  expr = caseExpr <|> letExpr <|> doExpr <|> bin 0 False
  bin 10 _ = molecule
  bin prec isR = rec False =<< bin (prec + 1) False where
    rec isL m = (try $ do
      o <- varSym <|> between (want "`") (want "`") varStr
      let (a, p) = fixity o
      when (p /= prec) $ fail ""
      case a of
        LAssoc -> do
          when isR $ fail "same precedence, mixed associativity"
          n <- bin (prec + 1) False
          rec True $ Ast $ Ast (Ast (Var o) :@ m) :@ n
        NAssoc -> do
          n <- bin (prec + 1) False
          pure $ Ast $ Ast (Ast (Var o) :@ m) :@ n
        RAssoc -> do
          when isL $ fail "same precedence, mixed associativity"
          n <- bin prec True
          pure $ Ast $ Ast (Ast (Var o) :@ m) :@ n
      ) <|> pure m
  letDefn = do
    s <- varStr
    void $ want "="
    ast <- expr
    pure (s, ast)
  doExpr = do
    void $ want "do"
    ss <- between (want "{") (want "}") $ stmt `sepBy` want ";"
    case ss of
      [] -> fail "empty do block"
      ((mv, x):t) -> desugarDo x mv t
  desugarDo x Nothing [] = pure x
  desugarDo _ _ [] = fail "do block ends with (<-) statement"
  desugarDo x mv ((mv1, x1):rest) = do
    body <- desugarDo x1 mv1 rest
    pure $ Ast $ Ast (Ast (Var ">>=") :@ x) :@ Ast (Lam [fromMaybe "_" mv] body)
  stmt = do
    v <- expr
    lArrStmt v <|> pure (Nothing, v)
  lArrStmt v = want "<-" >> case v of
    Ast (Var s) -> do
      x <- expr
      pure (Just s, x)
    _ -> fail "want variable on left of (<-)"
  letExpr = do
    ds <- between (want "let") (want "in") $
      between (want "{") (want "}") $ letDefn `sepBy` want ";"
    Ast . Let ds <$> expr
  caseExpr = do
    x <- between (want "case") (want "of") expr
    as <- catMaybes <$> between (want "{") (want "}") (alt `sepBy` want ";")
    when (null as) $ fail "empty case"
    pure $ Ast $ Cas x as
  alt = try (do
    p <- expr
    void $ want "->"
    x <- expr
    pure $ Just (p, x)) <|> pure Nothing
  lambda = fmap Ast $ Lam <$> between (want "\\") (want "->") (many1 varStr) <*> expr
  molecule = lambda <|> foldl1' ((Ast .) . (:@)) <$> many1 atom
  var = Ast . Var <$> varStr
  atom = preOp <|> tup <|> call <|> qvar <|> var <|> num <|> str
    <|> lis <|> enumLis
  preOp = try $ Ast . Var <$> between (want "(") (want ")") varSym
  tup = do
    xs <- between (want "(") (want ")") $ expr `sepBy` want ","
    pure $ case xs of  -- Abuse Pack to represent tuples.
      [] -> Ast $ Pack 0 0
      [x] -> x
      _ -> foldl' ((Ast .) . (:@)) (Ast $ Pack 0 $ length xs) xs
  enumLis = try $ between (want "[") (want "]") $ do
    a <- expr
    void $ want ".."
    b <- expr
    pure $ Ast $ Ast (Ast (Var "enumFromTo") :@ a) :@ b
  lis = try $ do
    items <- between (want "[") (want "]") $ expr `sepBy` want ","
    pure $ foldr (\a b -> Ast (Ast (Ast (Var ":") :@ a) :@ b)) (Ast $ Var "[]") items
  splitDot s = second tail $ splitAt (fromJust $ elemIndex '.' s) s
  qvar = try $ do
    (t, s) <- tok
    when (t /= LexQual) $ fail ""
    pure $ Ast $ uncurry Qual $ splitDot s
  call = do
    void $ want "call"
    (t, s) <- tok
    case t of
      LexQual -> pure $ Ast $ uncurry CCall $ splitDot s
      LexVar  -> pure $ Ast $ CCall "" s
      _ -> fail "bad call"
  num = try $ do
    (t, s) <- tok
    when (t /= LexNumber) $ fail ""
    pure $ Ast $ I $ read s
  str = try $ do
    (t, s) <- tok
    when (t /= LexString) $ fail ""
    pure $ Ast $ S $ pack $ c2w <$> s
  varSym = do
    (t, s) <- tok
    when (t /= LexSymbol || s `elem` ["..", "::", "=", "|", "<-", "->", "=>"]) $ fail ""
    pure s

varStr :: Parser String
varStr = try $ do
  (t, s) <- tok
  when (t /= LexVar || s `elem` words "case of let where do in call") $ fail ""
  pure s

want :: String -> Parser String
want t = expect <|> autoCloseBrace where
  autoCloseBrace = if t /= "}" then fail "" else do
    (ty, x) <- lookAhead tok
    if ty == LexSpecial && x == ")" || x == "]" then do
      (st, is) <- getState
      case is of
        (m:ms) | m /= 0 -> do
          putState (st, ms)
          pure "}"
        _ -> fail "missing }"
    else fail "missing }"
  expect = try $ do
    (ty, s) <- tok
    unless (ty /= LexString && s == t) $ fail $ "expected " ++ t
    pure s

data LexemeType = LexString | LexNumber | LexVar | LexSpecial | LexSymbol | LexQual | LexEOF deriving (Eq, Show)
type Lexeme = (LexemeType, String)

-- | Layout-aware lexer.
-- See https://www.haskell.org/onlinereport/haskell2010/haskellch10.html
tok :: Parser Lexeme
tok = do
  filler
  (st, is) <- getState
  let
    autoContinueBrace n = case is of
      (m : _)  | m == n -> pure (LexSpecial, ";")
      (m : ms) | n < m -> do
        putState (IndentAgain n, ms)
        pure (LexSpecial, "}")
      _ -> rawTok
    explicitBrace = try $ do
      r <- rawTok
      when (r /= (LexSpecial, "{")) $ fail "bad indentation"
      putState (LineMiddle, 0:is)
      pure r
    end = do
      eof
      case is of
        0:_ -> fail "unmatched '{'"
        [] -> pure (LexEOF, "")
        _:ms -> do
          putState (st, ms)
          pure (LexSpecial, "}")
  end <|> case st of
    IndentAgain col -> do
      putState (LineMiddle, is)
      autoContinueBrace col
    LineStart -> do
      col <- sourceColumn <$> getPosition
      putState (LineMiddle, is)
      autoContinueBrace col
    AwaitBrace -> explicitBrace <|> do
      n <- sourceColumn <$> getPosition
      case is of
        (m : _) | n > m -> do
          putState (LineMiddle, n : is)
          pure (LexSpecial, "{")
        [] | n > 0 -> do
          putState (LineMiddle, [n])
          pure (LexSpecial, "{")
        -- Empty blocks unsupported (see Note 2 in above link).
        _ -> fail "TODO"
    _ -> do
      r <- rawTok
      when (r == (LexSpecial, "}")) $ case is of
        (0 : _) -> modifyState $ second tail
        _ -> fail "unmatched }"
      pure r

rawTok :: Parser Lexeme
rawTok = do
  r <- symbol <|> ident <|> special <|> str
  pure r
  where
  ident = do
    s <- many1 (alphaNum <|> char '_')
    (try $ do
      void $ char '.'
      v <- many1 (alphaNum <|> char '_')
      pure (LexQual, s ++ '.':v)) <|> do
      when (s `elem` ["let", "where", "do", "of"]) $ do
        (_, is) <- getState
        putState (AwaitBrace, is)
      -- Allowing hashes to refer to contracts means identifiers can start
      -- with digits. We may want to change this.
      if all isDigit s
      then pure (LexNumber, s)
      else pure (LexVar, s)
  special = (,) LexSpecial <$> foldl1' (<|>) (string . pure <$> "(),;[]`{}")
  symbol = (,) LexSymbol <$> many1 (oneOf "!#$%&*+./<=>?@\\^|-~:")
  str = do
    void $ char '"'
    s <- many $ (char '\\' >> escapes) <|> noneOf "\""
    void $ char '"'
    pure (LexString, s)
  escapes = foldl1' (<|>)
    [ char '\\' >> pure '\\'
    , char '"' >> pure '"'
    , char 'n' >> pure '\n'
    ]

filler :: Parser ()
filler = void $ many $ void (char ' ') <|> nl <|> com
  where
  hsNewline = (void $ try $ string "\r\n") <|> (void $ oneOf "\r\n\f")
  com = do
    void $ between (try $ string "--") hsNewline $ many $ noneOf "\r\n\f"
    (st, is) <- getState
    when (st == LineMiddle) $ putState (LineStart, is)
  nl = do
    hsNewline
    (st, is) <- getState
    when (st == LineMiddle) $ putState (LineStart, is)

data AstPlus = AstPlus
  { exports :: [String]
  , wdecls :: [String]
  , storages :: [String]
  , asts :: [(String, Ast)]
  , funTypes :: [(String, QualType)]
  } deriving Show

contract :: Parser AstPlus
contract = do
  es <- option [] $ try $ want "contract" >>
    (between (want "(") (want ")") $ varStr `sepBy` want ",")
  ws <- option [] $ try $ want "wdecl" >>
    (between (want "(") (want ")") $ varStr `sepBy` want ",")
  ms <- option [] $ try $ want "storage" >>
    (between (want "(") (want ")") $ varStr `sepBy` want ",")
  putState (AwaitBrace, [])
  ds <- supercombinators
  when (isNothing $ mapM (`lookup` ds) es) $ fail "bad exports"
  when (isNothing $ mapM (`lookup` ds) ws) $ fail "bad wdecls"
  pure $ AstPlus es ws ms ds []

lexOffside :: String -> Either ParseError [String]
lexOffside = fmap (fmap snd) <$> runParser tokUntilEOF (AwaitBrace, []) "" where
  tokUntilEOF = do
    t <- tok
    case fst t of
      LexEOF -> pure []
      _ -> (t:) <$> tokUntilEOF

parseDefs :: String -> Either ParseError [(String, Ast)]
parseDefs = runParser program (AwaitBrace, []) ""

parseContract :: String -> Either ParseError AstPlus
parseContract = fmap maybeAddMain . runParser contract (Boilerplate, []) ""

maybeAddMain :: AstPlus -> AstPlus
maybeAddMain a = case lookup "main" $ asts a of
  Nothing -> a { asts = ("main",
    Ast $ Ast (Var "pure") :@ Ast (Pack 0 0)):asts a }
  Just _  -> a

-- The Constraints monad combines a State monad and an Either monad.
-- The state consists of the set of constraints and next integer available
-- for naming a free variable, and the contexts of each variable.
data ConState = ConState Int [(Type, Type)] (Map String [String])
data Constraints a = Constraints (ConState -> Either String (a, ConState))

instance Functor Constraints where fmap = liftM
instance Applicative Constraints where
  (<*>) = ap
  pure = return

instance Monad Constraints where
  Constraints c1 >>= fc2 = Constraints $ \cs -> case c1 cs of
    Left err -> Left err
    Right (r, cs2) -> let Constraints c2 = fc2 r in c2 cs2
  return a = Constraints $ \p -> Right (a, p)

newTV :: Constraints Type
newTV = Constraints $ \(ConState i cs m) -> Right (TV $ "_" ++ show i, ConState (i + 1) cs m)

addConstraint :: (Type, Type) -> Constraints ()
addConstraint c = Constraints $ \(ConState i cs m) -> Right ((), ConState i (c:cs) m)

addContext :: String -> String -> Constraints ()
addContext s x = Constraints $ \(ConState i cs m) -> Right ((), ConState i cs $ M.insertWith union x [s] m)

type Globals = Map String (Maybe (Int, Int), Type)
type QualType = (Type, [(String, String)])

-- | Gathers constraints.
-- Replaces overloaded methods with Placeholder.
-- Replaces data constructors with Pack.
gather
  :: (String -> String -> Either String Type)
  -> Globals
  -> [(String, QualType)]
  -> Ast
  -> Constraints (AAst Type)
gather findExport prelude env (Ast ast) = case ast of
  I i -> pure $ AAst (TC "Int") $ I i
  S s -> pure $ AAst (TC "String") $ S s
  Pack m n -> do  -- Only tuples are pre`Pack`ed.
    xs <- replicateM n newTV
    let r = foldl' (TApp) (TC "()") xs
    pure $ AAst (foldr (:->) r xs) $ Pack m n
  Var "_" -> do
    x <- newTV
    pure $ AAst x $ Var "_"
  Var v -> case lookup v env of
    Just qt  -> do
      (t1, qs1) <- instantiate qt
      pure $ foldl' ((AAst t1 .) . (:@)) (AAst t1 $ Var v) $ (\(a, b) -> AAst (TC $ "Dict-" ++ a) $ Placeholder a (TV b)) <$> qs1
    Nothing -> case M.lookup v methods of
      Just qt -> do
        (t1, [(_, x)]) <- instantiate qt
        pure $ AAst t1 $ Placeholder v $ TV x
      Nothing -> case M.lookup v prelude of
        Just (ma, gt) -> flip AAst (maybe (Var v) (uncurry Pack) ma) . fst <$> instantiate (gt, [])
        Nothing       -> bad $ "undefined: " ++ v
  t :@ u -> do
    a@(AAst tt _) <- rec env t
    b@(AAst uu _) <- rec env u
    x <- newTV
    addConstraint (tt, uu :-> x)
    pure $ AAst x $ a :@ b
  Lam args u -> do
    ts <- mapM (const newTV) args
    a@(AAst tu _) <- rec ((zip (filter (/= "_") args) $ zip ts $ repeat []) ++ env) u
    pure $ AAst (foldr (:->) tu ts) $ Lam args a
  Cas e as -> do
    aste@(AAst te _) <- rec env e
    x <- newTV
    astas <- forM as $ \(p, a) -> do
      let
        varsOf (Ast (t :@ u)) = varsOf t ++ varsOf u
        varsOf (Ast (Var v)) | isLower (head v) = [v]
        varsOf _ = []
      when (varsOf p /= nub (varsOf p)) $ bad "multiple binding in pattern"
      envp <- forM (varsOf p) $ \s -> (,) s . flip (,) [] <$> newTV
      -- TODO: Check p is a pattern.
      astp@(AAst tp _) <- rec (envp ++ env) p
      addConstraint (te, tp)
      asta@(AAst ta _) <- rec (envp ++ env) a
      addConstraint (x, ta)
      pure (astp, asta)
    pure $ AAst x $ Cas aste astas
  Let ds body -> do
    es <- forM (fst <$> ds) $ \s -> (,) s <$> newTV
    let envLet = (second (flip (,) []) <$> es) ++ env
    ts <- forM (snd <$> ds) $ rec envLet
    mapM_ addConstraint $ zip (snd <$> es) (afst <$> ts)
    body1@(AAst t _) <- rec envLet body
    pure $ AAst t $ Let (zip (fst <$> ds) ts) body1
  -- TODO: Type classes for CCall and Qual.
  CCall c f -> case findExport c f of
    Left err -> bad err
    Right t -> flip AAst (CCall c f) . (TC "String" :->) . fst <$> instantiate (t, [])
  Qual c f -> case findExport c f of
    Left err -> bad err
    Right t -> flip AAst (Qual c f) . fst <$> instantiate (t, [])
  _ -> fail $ "BUG! unhandled: " ++ show ast
  where
    rec = gather findExport prelude
    bad = Constraints . const . Left
    afst (AAst t _) = t

-- | Instantiate generalized variables.
-- Returns type where all generalized variables have been instantiated along
-- with the list of type constraints where each generalized variable has
-- been instantiated with the same generated names.
instantiate :: QualType -> Constraints (Type, [(String, String)])
instantiate (ty, qs) = do
  (gvmap, result) <- f [] ty
  let qInstances = second (getVar gvmap) <$> qs
  forM_ qInstances $ uncurry addContext
  pure (result, qInstances)
  where
  getVar m v = x where Just (TV x) = lookup v m
  f m (GV s) | Just t <- lookup s m = pure (m, t)
             | otherwise = do
               x <- newTV
               pure ((s, x):m, x)
  f m (t :-> u) = do
    (m1, t') <- f m t
    (m2, u') <- f m1 u
    pure $ (m2, t' :-> u')
  f m (t `TApp` u) = do
    (m1, t') <- f m t
    (m2, u') <- f m1 u
    pure $ (m2, t' `TApp` u')
  f m t = pure (m, t)

generalize :: [(String, Type)] -> Map String [String] -> AAst Type -> (QualType, Ast)
generalize soln ctx a0@(AAst t0 _) = ((t, qs), dictSolve dsoln soln ast) where
  (t, qs) = runState (generalize' ctx $ typeSolve soln t0) []
  dsoln = zip qs $ ("#d" ++) . show <$> [(0::Int)..]
  ast = case deAnn a0 of
    Ast (Lam ss body) -> Ast $ Lam (dvars ++ ss) body
    body -> Ast $ Lam dvars body
    where dvars = snd <$> dsoln

generalize' :: Map String [String] -> Type -> State [(String, String)] Type
generalize' ctx ty = case ty of
  TV s -> do
    case M.lookup s ctx of
      Just cs -> modify' $ union $ flip (,) s <$> cs
      Nothing -> pure ()
    pure $ GV s
  u :-> v  -> (:->) <$> generalize' ctx u <*> generalize' ctx v
  TApp u v -> TApp  <$> generalize' ctx u <*> generalize' ctx v
  _        -> pure ty

freeTV :: Type -> [String]
freeTV (TApp a b) = freeTV a ++ freeTV b
freeTV (a :-> b)  = freeTV a ++ freeTV b
freeTV (TV tv)    = [tv]
freeTV _          = []

subst :: (String, Type) -> Type -> Type
subst (x, t) ty = case ty of
  TApp a b      -> subst (x, t) a `TApp` subst (x, t) b
  a :-> b       -> subst (x, t) a :-> subst (x, t) b
  TV y | x == y -> t
  _             -> ty

methods :: Map String (Type, [(String, String)])
methods = M.fromList
  [ ("==", (a :-> a :-> TC "Bool", [("Eq", "a")]))
  , (">>=", (TApp m a :-> (a :-> TApp m b)  :-> TApp m b, [("Monad", "m")]))
  , ("pure", (a :-> TApp m a, [("Monad", "m")]))
  , ("save", (a :-> TC "String", [("Save", "a")]))
  , ("load", (TC "String" :-> a, [("Save", "a")]))
  ] where
    a = GV "a"
    b = GV "b"
    m = GV "m"

listEqHack :: (String, Ast)
listEqHack = r where Right [r] = parseDefs "list_eq_instance d a b = case a of { [] -> case b of {[] -> True; w -> False}; (x:xs) -> case b of { [] -> False; (y:ys)-> (d x y) && list_eq_instance d xs ys } }"

maybePureHack :: (String, Ast)
maybePureHack = r where Right [r] = parseDefs "maybe_pure x = Just x"

maybeMonadHack :: (String, Ast)
maybeMonadHack = r where Right [r] = parseDefs "maybe_monad x f = case x of { Nothing -> Nothing; Just a -> f a }"

-- This works because it's post-type-checking.
ioPureHack :: (String, Ast)
ioPureHack = r where Right [r] = parseDefs "io_pure x rw = (x, rw)"

ioMonadHack :: (String, Ast)
ioMonadHack = r where Right [r] = parseDefs "io_monad f g rw = let {p = f rw} in case p of (a, rw1) -> g a rw1"

fstHack :: (String, Ast)
fstHack = r where Right [r] = parseDefs "fst p = case p of (x, y) -> x"

sndHack :: (String, Ast)
sndHack = r where Right [r] = parseDefs "snd p = case p of (x, y) -> y"

dictSolve :: [((String, String), String)] -> [(String, Type)] -> Ast -> Ast
dictSolve dsoln soln (Ast ast) = case ast of
  u :@ v  -> Ast $ rec u :@ rec v
  Lam ss a -> Ast $ Lam ss $ rec a
  Cas e alts -> Ast $ Cas (rec e) $ (id *** rec) <$> alts

  Placeholder ">>=" t -> Ast $ Ast (Var "snd") :@ rec (Ast $ Placeholder "Monad" $ typeSolve soln t)
  Placeholder "pure" t -> Ast $ Ast (Var "fst") :@ rec (Ast $ Placeholder "Monad" $ typeSolve soln t)

  Placeholder "==" t -> rec $ Ast $ Placeholder "Eq" $ typeSolve soln t
  Placeholder "save" t -> Ast $ Ast (Var "fst") :@ rec (Ast $ Placeholder "Save" $ typeSolve soln t)
  Placeholder "load" t -> Ast $ Ast (Var "snd") :@ rec (Ast $ Placeholder "Save" $ typeSolve soln t)
  Placeholder d t -> case typeSolve soln t of
    TV v -> Ast $ Var $ fromJust $ lookup (d, v) dsoln
    u -> Ast $ findInstance d u
  _       -> Ast ast
  where
    rec = dictSolve dsoln soln
    findInstance "Eq" t = case t of
      TC "String"        -> Var "String-=="
      TC "Int"           -> Var "Int-=="
      TApp (TC "List") a -> Ast (Var "list_eq_instance") :@ rec (Ast $ Placeholder "Eq" a)
      e -> error $ "BUG! no Eq for " ++ show e
    findInstance "Save" t = case t of
      TC "String" -> Ast (Ast (Pack 0 2) :@ Ast (Var "String-save")) :@ Ast (Var "String-load")
      TC "Int" -> Ast (Ast (Pack 0 2) :@ Ast (Var "Int-save")) :@ Ast (Var "Int-load")
      e -> error $ "BUG! no Save for " ++ show e
    findInstance "Monad" t = case t of
      TC "Maybe" -> Ast (Ast (Pack 0 2) :@ Ast (Var "maybe_pure")) :@ Ast (Var "maybe_monad")
      TC "IO" -> Ast (Ast (Pack 0 2) :@ Ast (Var "io_pure")) :@ Ast (Var "io_monad")
      e -> error $ "BUG! no Monad for " ++ show e
    findInstance d _ = error $ "BUG! bad class: " ++ show d

typeSolve :: [(String, Type)] -> Type -> Type
typeSolve soln t = foldl' (flip subst) t soln

-- | The `propagateClasses` and `propagateClassTyCon` functions of
-- "Implementing type classes".
propagate :: [String] -> Type -> StateT (Map String [String]) (Either String) ()
propagate cs (TV y) = modify' $ M.insertWith union y cs
propagate cs t = mapM_ propagateTyCon cs where
  propagateTyCon "Eq" = case t of
    TC "Int" -> pure ()
    TC "String" -> pure ()
    TApp (TC "List") a -> propagate ["Eq"] a
    _ -> lift $ Left $ "no Eq instance: " ++ show t
  propagateTyCon "Monad" = case t of
    TC "Maybe" -> pure ()
    TC "IO" -> pure ()
    _ -> lift $ Left $ "no Monad instance: " ++ show t
  propagateTyCon c = error $ "TODO: " ++ c

-- TODO: Apply substitutions for friendlier messages.
unify :: [(Type, Type)] -> StateT (Map String [String]) (Either String) [(String, Type)]
unify [] = pure []
unify ((GV _, _):_) = lift $ Left "BUG! generalized variable in constraint"
unify ((_, GV _):_) = lift $ Left "BUG! generalized variable in constraint"
unify ((s, t):cs) | s == t = unify cs
unify ((TV x, t):cs)
  | x `elem` freeTV t = lift $ Left $ "infinite: " ++ x ++ " = " ++ show t
  | otherwise         = do
    -- | The `instantiateTyvar` function of "Implementing type classes".
    m <- get
    propagate (fromMaybe [] $ M.lookup x m) t
    fmap ((x, t):) $ unify $ join (***) (subst (x, t)) <$> cs
unify ((s, t@(TV _)):cs) = unify ((t, s):cs)
unify ((TApp s1 s2, TApp t1 t2):cs) = unify ((s1, t1):(s2, t2):cs)
unify (( s1 :-> s2, t1 :-> t2):cs)  = unify ((s1, t1):(s2, t2):cs)
unify ((s, t):_) = lift $ Left $ "mismatch: " ++ show s ++ " /= " ++ show t

preludeMinimal :: Map String (Maybe (Int, Int), Type)
preludeMinimal = M.fromList $ (second ((,) Nothing) <$>
  [ ("+", TC "Int" :-> TC "Int" :-> TC "Int")
  , ("-", TC "Int" :-> TC "Int" :-> TC "Int")
  , ("*", TC "Int" :-> TC "Int" :-> TC "Int")
  , ("div", TC "Int" :-> TC "Int" :-> TC "Int")
  , ("mod", TC "Int" :-> TC "Int" :-> TC "Int")
  , ("<", TC "Int" :-> TC "Int" :-> TC "Bool")
  , (">", TC "Int" :-> TC "Int" :-> TC "Bool")
  , ("<=", TC "Int" :-> TC "Int" :-> TC "Bool")
  , (">=", TC "Int" :-> TC "Int" :-> TC "Bool")
  , ("&&", TC "Bool" :-> TC "Bool" :-> TC "Bool")
  , ("||", TC "Bool" :-> TC "Bool" :-> TC "Bool")
  , ("++", TC "String" :-> TC "String" :-> TC "String")
  , ("undefined", a)
  -- | Programmers cannot call the following directly.
  -- We keep their types around for various checks.
  , ("Int-==", TC "Int" :-> TC "Int" :-> TC "Bool")
  , ("String-==", TC "String" :-> TC "String" :-> TC "Bool")
  ]) ++
  [ ("False",   (jp 0 0, TC "Bool"))
  , ("True",    (jp 1 0, TC "Bool"))
  , ("Nothing", (jp 0 0, TApp (TC "Maybe") a))
  , ("Just",    (jp 1 1, a :-> TApp (TC "Maybe") a))
  , ("Left",    (jp 0 1, a :-> TApp (TApp (TC "Either") a) b))
  , ("Right",   (jp 1 1, b :-> TApp (TApp (TC "Either") a) b))
  , ("[]",      (jp 0 0, TApp (TC "List") a))
  , (":",       (jp 1 2, a :-> TApp (TC "List") a :-> TApp (TC "List") a))
  ]
  where
    jp m n = Just (m, n)
    a = GV "a"
    b = GV "b"

arityFromType :: Type -> Int
arityFromType = f 0 where
  f acc (_ :-> r) = f (acc + 1) r
  f acc _ = acc

-- TODO: These dictionaries should not be built-in!
hacks :: [(String, Ast)]
hacks =
 [ fstHack
 , sndHack
 , maybePureHack
 , maybeMonadHack
 , ioPureHack
 , ioMonadHack
 , listEqHack
 ]

{-
unAst :: Ast -> AstF Ast
unAst (Ast a) = a
-}

expandSyscalls :: ExternType -> [(String, Int)] -> Ast -> Ast
expandSyscalls ext arities = ffix $ \rec (Ast ast) -> Ast $ case ast of
{-
  Cas (Ast x) as -> Cas (Ast $ rec x) (second (Ast . rec. unAst) <$> as)
-}
  -- Example:
  --  target.fun 1 2 "three"
  -- becomes:
  --  #nfsyscall 6 0 "target" "fun" 3 1 2 "three"
  Qual c f | Just n <- ext c f -> foldl1' appIt [Var "#nfsyscall", I (fromIntegral $ n + 3), I 0, S (pack $ c2w <$> c), S (pack $ c2w <$> f), I (fromIntegral n)]
  -- Example:
  --  call target.fun "abc123" 1 2 "three"
  --  call fun "abc123" 1 2 "three"
  -- becomes:
  --  #nfsyscall 7 8 "target" "fun" 3 "abc123" 1 2 "three"
  --  #nfsyscall 6 9 "fun" 3 "abc123" 1 2 "three"
  CCall "" f | Just n <- lookup f arities -> foldl1' appIt [Var "#nfsyscall", I (fromIntegral $ n + 3), I 9, S (pack $ c2w <$> f), I (fromIntegral n)]
  CCall c f | Just n <- ext c f -> foldl1' appIt [Var "#nfsyscall", I (fromIntegral $ n + 4), I 8, S (pack $ c2w <$> c), S (pack $ c2w <$> f), I (fromIntegral n)]
  _ -> rec ast
  where appIt x y = Ast x :@ Ast y

getContractExport :: ExternType -> [String] -> String -> String -> Either String Type
getContractExport _ es "" v = if v `elem` es
  then Right $ TV $ '*':v
  else Left $ "no such export " ++ v
getContractExport f _ c v = case f c v of
  Nothing -> Left $ "no such export " ++ c ++ "." ++ v
  Just n -> Right $ foldr (:->) (TC "IO" `TApp` GV "r") [GV $ "x" ++ show i | i <- [1..n]]

hsToAst :: Map String (Maybe (Int, Int), Type) -> ExternType -> String -> Either String AstPlus
hsToAst boostMap ext prog = do
  a@(AstPlus es _ storage ds _) <- showErr $ parseContract prog
  (preStorageInferred, storageCons) <- inferType (getContractExport ext es) (genTypes storage) (ds ++ hacks)
  let
    inferred = constrainStorage storageCons preStorageInferred
    arities = second (countArgs . fst . fst) <$> inferred
    countArgs (_ :-> b) = 1 + countArgs b
    countArgs _ = 0
    transform = expandSyscalls ext arities . expandCase
    subbedDefs = (second transform <$>) . liftLambdas . (second snd <$>) $ inferred
    types = second fst <$> inferred
  pure a { asts = subbedDefs, funTypes = types }
  where
    showErr = either (Left . show) Right
    genTypes storage = preludeMinimal
      `M.union` boostMap
      `M.union` (M.fromList $ storageTypeConstraintHack <$> storage)
    storageTypeConstraintHack s = (s, (Nothing, TC "Map" `TApp` TV ('@':s)))

constrainStorage :: [(String, Type)] -> [(String, (QualType, Ast))] -> [(String, (QualType, Ast))]
constrainStorage cons ds = second (first (first rewriteType)) <$> ds where
  rewriteType (GV ('@':x)) = case typeSolve cons $ TV ('@':x) of
    TC t -> TC t
    _    -> TC "String"
  rewriteType (t :-> u) = rec t :-> rec u
  rewriteType (TApp t u) = TApp (rec t) (rec u)
  rewriteType t = t
  rec = rewriteType

inferType
  :: (String -> String -> Either String Type)
  -> Globals
  -> [(String, Ast)]
  -- | Returns types of definitions and storage maps.
  -> Either String ([(String, (QualType, Ast))], [(String, Type)])
inferType findExport globs ds = foldM inferMutual ([], []) $ map (map (\k -> (k, fromJust $ lookup k ds))) sortedDefs where
  -- Groups of definitions, sorted in the order we should infer their types.
  sortedDefs = reverse $ scc (callees ds) $ fst <$> ds
  inferMutual :: ([(String, (QualType, Ast))], [(String, Type)]) -> [(String, Ast)] -> Either String ([(String, (QualType, Ast))], [(String, Type)])
  inferMutual (acc, accStorage) grp = do
    (bs, ConState _ cs m) <- buildConstraints $ do
      ts <- mapM (gather findExport globs env) $ snd <$> grp
      when ("main" `elem` (fst <$> grp)) $ do
        r <- newTV
        addConstraint (TV "*main", TApp (TC "IO") r)
      mapM_ addConstraint $ zip tvs $ annOf <$> ts
      pure ts
    (soln, ctx) <- runStateT (unify cs) m
    let storageCons = second (typeSolve soln) <$> filter (('@' ==) . head . fst) soln
    -- TODO: Look for conflicting storage constraints.
    -- TODO: The `generalize` stage removes type annotations. May be
    -- beneficial to keep them around longer.
    pure ((++ acc) $ zip (fst <$> grp) $ generalize soln ctx <$> bs, accStorage ++ storageCons)
    where
      annOf (AAst a _) = a
      buildConstraints (Constraints f) = f $ ConState 0 [] M.empty
      tvs = TV . ('*':) . fst <$> grp
      env = zip (fst <$> grp) (zip tvs $ repeat $ []) ++ map (second fst) acc

callees :: [(String, Ast)] -> String -> [String]
callees ds f = deps f (fromJust $ lookup f ds) where
  deps name (Ast body) = case body of
    Lam ss t | name `notElem` ss -> rec t
    -- TODO: Look for shadowed function name in case and let statements.
    -- Or add deshadowing phase.
    CCall "" v         -> [v]
    Cas x as          -> rec x ++ concatMap rec (snd <$> as)
    Let as x          -> rec x ++ concatMap rec (snd <$> as)
    x :@ y            -> rec x ++ rec y
    Var v | v /= name -> case lookup v ds of
      Nothing -> []
      Just _  -> [v]
    _                 -> []
    where rec = deps name

-- | Returns strongly connected components in topological order.
scc :: Eq a => (a -> [a]) -> [a] -> [[a]]
scc suc vs = foldl' (\cs v -> assign cs [] v : cs) [] $ reverse $ topo suc vs where
  assign cs c v | any (elem v) $ c:cs = c
                | otherwise           = foldl' (assign cs) (v:c) (suc v)

topo :: Eq a => (a -> [a]) -> [a] -> [a]
topo suc vs = fst $ foldl' visit ([], []) vs where
  visit (done, doing) v
    | v `elem` done || v `elem` doing = (done, doing)
    | otherwise = (\(xs, x:ys) -> (x:xs, ys)) $
      foldl' visit (done, v:doing) (suc v)

freeV :: [(String, Ast)] -> [(String, AAst [String])]
freeV scs = map f scs where
  f (d, Ast ast) = (d, g [] ast)
  g :: [String] -> AstF Ast -> AAst [String]
  g cand (Lam ss (Ast a)) = AAst (vs \\ ss) $ Lam ss a1 where
    a1@(AAst vs _) = g (union cand ss) a
  g cand (Ast x :@ Ast y) = AAst (xv `union` yv) $ x1 :@ y1 where
    x1@(AAst xv _) = g cand x
    y1@(AAst yv _) = g cand y
  g cand (Var v) | v `elem` cand = AAst [v] $ Var v
                 | otherwise     = AAst []  $ Var v
  g cand (Cas (Ast x) as) = AAst (foldl' union xv $ fst <$> as1) $ Cas x1 $ snd <$> as1 where
    x1@(AAst xv _) = g cand x
    as1 = map h as
    h (Ast p, Ast e) = (vs1, (g [] p, e1)) where
      e1@(AAst vs _) = g (cand `union` caseVars p) e
      vs1 = vs \\ caseVars p
  g cand (Let ds (Ast e)) = AAst (ev \\ binders) $ Let ds1 e1 where
    e1@(AAst ev _) = g (cand `union` binders) e
    binders = fst <$> ds
    ds1 = map h ds
    h (s, Ast x) = (s, g (cand `union` binders) x)
  g _    (I i) = AAst [] $ I i
  g _    (S s) = AAst [] $ S s
  g _    (Pack m n) = AAst [] $ Pack m n
  g _    (Qual x y) = AAst [] $ Qual x y
  g _    (CCall x y) = AAst [] $ CCall x y
  g _    (Placeholder x y) = AAst [] $ Placeholder x y

caseVars :: AstF Ast -> [String]
caseVars (Var v) = [v]
caseVars (Ast x :@ Ast y) = caseVars x `union` caseVars y
caseVars _ = []

liftLambdas :: [(String, Ast)] -> [(String, Ast)]
liftLambdas scs = existingDefs ++ newDefs where
  (existingDefs, (_, newDefs)) = runState (mapM f $ freeV scs) ([], [])
  f (s, (AAst _ (Lam args body))) = do
    modify $ first $ const [s]
    body1 <- g body
    pure (s, Ast $ Lam args body1)
  f _ = error "bad top-level definition"
  genName :: State ([String], [(String, Ast)]) String
  genName = do
    (names, ys) <- get
    let
      n = head $ filter (`notElem` names) $
        (++ ('$':last names)) . show <$> [(0::Int)..]
    put (n:names, ys)
    pure n
  g (AAst _ (x :@ y)) = fmap Ast $ (:@) <$> g x <*> g y
  g (AAst _ (Let ds t)) = fmap Ast $ Let <$> mapM noLamb ds <*> g t where
    noLamb (name, (AAst fvs (Lam ss body))) = do
      n <- genName
      body1 <- g body
      modify $ second ((n, Ast $ Lam (fvs ++ ss) body1):)
      pure (name, foldl' ((Ast .) . (:@)) (Ast $ Var n) $ Ast . Var <$> fvs)
    noLamb (name, a) = (,) name <$> g a
  g (AAst fvs lam@(Lam _ _)) = do
    n <- genName
    g $ AAst fvs $ Let [(n, AAst fvs lam)] (AAst [n] $ Var n)
  g (AAst _ (Cas expr as)) =
    fmap Ast $ Cas <$> g expr <*> mapM (\(p, t) -> (,) <$> g p <*> g t) as
  g ann = pure $ deAnn ann

expandCase :: Ast -> Ast
expandCase = ffix $ \h (Ast ast) -> Ast $ case ast of
  Cas e alts -> dupCase (rec e) alts
  _ -> h ast
  where
    rec = expandCase

    dupCase e [a] = Cas e $ evalState (expandAlt Nothing [] a) 0
    dupCase e (a:as) = Cas e $ evalState (expandAlt (Just $ rec $ Ast $ Cas e as) [] a) 0
    dupCase _ _ = error "BUG! no case alternatives"

    -- TODO: CCall `fromApList` only in last case alternative.
    expandAlt :: Maybe Ast -> [(Ast, Ast)] -> (Ast, Ast) -> State Int [(Ast, Ast)]
    expandAlt onFail deeper (p, a) = do
      case fromApList p of
        [Ast (Var _)] -> (:moreCases) . (,) p <$> g deeper a
        [Ast (S s)] -> do
          v <- genVar
          a1 <- g deeper a
          pure [(Ast $ Var v, Ast $ Cas (Ast (Ast (Ast (Var "String-==") :@ Ast (Var v)) :@ Ast (S s))) $ (Ast $ Pack 1 0, a1):moreCases)]
        [Ast (I n)] -> do
          v <- genVar
          a1 <- g deeper a
          pure [(Ast $ Var v, Ast $ Cas (Ast (Ast (Ast (Var "Int-==") :@ Ast (Var v)) :@ Ast (I n))) $ (Ast $ Pack 1 0, a1):maybe [] ((pure . (,) (Ast $ Pack 0 0))) onFail)]
        h@(Ast (Pack _ _)):xs -> (++ moreCases) <$> doPack [h] deeper xs a
        _ -> error $ "bad case: " ++ show p

      where
      moreCases = maybe [] ((pure . (,) (Ast $ Var "_"))) onFail
      doPack acc dpr [] body = (:moreCases) . (,) (foldl1 ((Ast .) . (:@)) acc) <$> g dpr body
      doPack acc dpr (h:rest) body = do
        gv <- Ast . Var <$> genVar
        case h of
          Ast (Var _) -> doPack (acc ++ [h]) dpr rest body
          _     -> doPack (acc ++ [gv]) (dpr ++ [(gv, h)]) rest body
      g [] body = pure body
      g ((v, w):rest) body = fmap Ast $ Cas v <$> expandAlt onFail rest (w, body)

    genVar = do
      n <- get
      put (n + 1)
      pure $ "c*" ++ show n

    fromApList :: Ast -> [Ast]
    fromApList (Ast (a :@ b)) = fromApList a ++ [b]
    fromApList a = [a]
