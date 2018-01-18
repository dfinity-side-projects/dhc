{-# LANGUAGE CPP #-}
{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PackageImports #-}
module DHC (parseContract, Syscalls, Ast(..), Type(..), inferType, parseDefs, lexOffside,
  preludeMinimal, hsToAst, liftLambdas) where

import Control.Arrow
import Control.DeepSeq (NFData(..))
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

instance Binary Ast
instance Binary Type

infixl 5 :@
data Ast = Qual String String | Call String String
  | Pack Int Int | I Int64 | S ShortByteString | Var String
  | Ast :@ Ast | Cas Ast [(Ast, Ast)]
  | Lam [String] Ast | Let [(String, Ast)] Ast
  | Placeholder String Type deriving (Read, Show, Generic)

infixr 5 :->
data Type = TC String | TApp Type Type | Type :-> Type
  | TV String | GV String deriving (Read, Show, Eq, Generic)

instance NFData Ast where
  rnf (Qual s1 s2) = rnf s1 `seq` rnf s2 `seq` ()
  rnf (Call s1 s2) = rnf s1 `seq` rnf s2 `seq` ()
  rnf (Pack i1 i2) = rnf i1 `seq` rnf i2 `seq` ()
  rnf (I i) = rnf i `seq` ()
  rnf (S s) = rnf s `seq` ()
  rnf (Var s) = rnf s `seq` ()
  rnf (a1 :@ a2) = rnf a1 `seq` rnf a2 `seq` ()
  rnf (Lam ss a) = rnf ss `seq` rnf a `seq` ()
  rnf (Cas a as) = rnf a `seq` rnf as `seq` ()
  rnf (Let ds a) = rnf ds `seq` rnf a `seq` ()
  rnf (Placeholder s t) = rnf s `seq` rnf t `seq` ()

instance NFData Type where
  rnf (TC s) = rnf s `seq` ()
  rnf (TApp t1 t2) = rnf t1 `seq` rnf t2 `seq` ()
  rnf (t1 :-> t2) = rnf t1 `seq` rnf t2 `seq` ()
  rnf (TV s) = rnf s `seq` ()
  rnf (GV s) = rnf s `seq` ()

type AnnAst ann = (ann, AnnAst' ann)
data AnnAst' ann
  = AnnVar String | AnnQual String String | AnnCall String String
  | AnnPack Int Int | AnnI Int64 | AnnS ShortByteString
  | AnnAst ann :@@ AnnAst ann
  | AnnCas (AnnAst ann) [(AnnAst ann, AnnAst ann)]
  | AnnLam [String] (AnnAst ann) | AnnLet [(String, AnnAst ann)] (AnnAst ann)
  | AnnPlaceholder String Type
  deriving Show

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
    Just . (,) fun . Lam args <$> expr) <|> pure Nothing
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
          rec True $ Var o :@ m :@ n
        NAssoc -> (Var o :@ m :@) <$> bin (prec + 1) False
        RAssoc -> do
          when isL $ fail "same precedence, mixed associativity"
          (Var o :@ m :@) <$> bin prec True
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
  desugarDo x (Just v) ((mv1, x1):rest) =
    desugarDo (Var ">>=" :@ x :@ Lam [v] x1) mv1 rest
  desugarDo x Nothing ((mv1, x1):rest) =
    desugarDo (Var ">>=" :@ x :@ Lam ["_"] x1) mv1 rest
  stmt = do
    v <- expr
    lArrStmt v <|> pure (Nothing, v)
  lArrStmt v = want "<-" >> case v of
    Var s -> do
      x <- expr
      pure (Just s, x)
    _ -> fail "want variable on left of (<-)"
  letExpr = do
    ds <- between (want "let") (want "in") $
      between (want "{") (want "}") $ letDefn `sepBy` want ";"
    Let ds <$> expr
  caseExpr = do
    x <- between (want "case") (want "of") expr
    as <- catMaybes <$> between (want "{") (want "}") (alt `sepBy` want ";")
    when (null as) $ fail "empty case"
    pure $ Cas x as
  lambda = Lam <$> between (want "\\") (want "->") (many1 varStr) <*> expr
  alt = try (do
    p <- expr  -- TODO: Restrict to patterns.
    void $ want "->"
    x <- expr
    pure $ Just (p, x)) <|> pure Nothing
  molecule = lambda <|> foldl1' (:@) <$> many1 atom
  atom = preOp <|> tup <|> call <|> qvar <|> var <|> num <|> str
    <|> lis <|> enumLis
  preOp = try $ Var <$> between (want "(") (want ")") varSym
  tup = do
    xs <- between (want "(") (want ")") $ expr `sepBy` want ","
    pure $ case xs of  -- Abuse Pack to represent tuples.
      [] -> Pack 0 0
      [x] -> x
      _ -> foldl' (:@) (Pack 0 $ length xs) xs
  enumLis = try $ between (want "[") (want "]") $ do
    a <- expr
    void $ want ".."
    b <- expr
    pure $ Var "enumFromTo" :@ a :@ b
  lis = try $ do
    items <- between (want "[") (want "]") $ expr `sepBy` want ","
    pure $ foldr (\a b -> Var ":" :@ a :@ b) (Var "[]") items
  var = Var <$> varStr
  splitDot s = second tail $ splitAt (fromJust $ elemIndex '.' s) s
  qvar = try $ do
    (t, s) <- tok
    when (t /= LexQual) $ fail ""
    pure $ uncurry Qual $ splitDot s
  call = do
    void $ want "call"
    (t, s) <- tok
    case t of
      LexQual -> pure $ uncurry Call $ splitDot s
      LexVar  -> pure $ Call "" s
      _ -> fail "bad call"
  num = try $ do
    (t, s) <- tok
    when (t /= LexNumber) $ fail ""
    pure $ I $ read s
  str = try $ do
    (t, s) <- tok
    when (t /= LexString) $ fail ""
    pure $ S $ pack $ c2w <$> s
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
  newlines = "\r\n\f"
  com = do
    void $ between (try $ string "--") ((void $ try $ string "\r\n") <|> (void $ oneOf newlines)) $ many $ noneOf newlines
    (st, is) <- getState
    when (st == LineMiddle) $ putState (LineStart, is)
  nl = do
    void $ char '\n'
    (st, is) <- getState
    when (st == LineMiddle) $ putState (LineStart, is)

contract :: Parser ([String], [String], [(String, Ast)])
contract = do
  es <- option [] $ try $ want "contract" >>
    (between (want "(") (want ")") $ varStr `sepBy` want ",")
  ms <- option [] $ try $ want "storage" >>
    (between (want "(") (want ")") $ varStr `sepBy` want ",")
  putState (AwaitBrace, [])
  ds <- supercombinators
  when (isNothing $ mapM (`lookup` ds) es) $ fail "bad exports"
  pure (es, ms, ds)

lexOffside :: String -> Either ParseError [String]
lexOffside = fmap (fmap snd) <$> runParser tokUntilEOF (AwaitBrace, []) "" where
  tokUntilEOF = do
    t <- tok
    case fst t of
      LexEOF -> pure []
      _ -> (t:) <$> tokUntilEOF

parseDefs :: String -> Either ParseError [(String, Ast)]
parseDefs = runParser program (AwaitBrace, []) ""

parseContract :: String -> Either ParseError ([String], [String], [(String, Ast)])
parseContract = runParser contract (Boilerplate, []) "" where

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
-- Replaces '==' with Placeholder.
-- Replaces data constructors with Pack.
gather
  :: (String -> String -> Either String Type)
  -> Globals
  -> [(String, QualType)]
  -> Ast
  -> Constraints (AnnAst Type)
gather findExport prelude env ast = case ast of
  I i -> pure (TC "Int", AnnI i)
  S s -> pure (TC "String", AnnS s)
  Var v -> case lookup v env of
    Just qt  -> if v `M.member` prelude then bad $ "ambiguous: " ++ v
      else do
        (t1, qs1) <- instantiate qt
        pure $ foldl' (((,) t1 .) .  (:@@)) (t1, AnnVar v) $ (\(a, b) -> (TC $ "Dict-" ++ a, AnnPlaceholder a (TV b))) <$> qs1
    Nothing -> case M.lookup v methods of
      Just qt -> do
        (t1, [(_, x)]) <- instantiate qt
        pure (t1, AnnPlaceholder v $ TV x)
      Nothing -> case M.lookup v prelude of
        Just (ma, gt) -> flip (,) (maybe (AnnVar v) (uncurry AnnPack) ma) . fst <$> instantiate (gt, [])
        Nothing       -> bad $ "undefined: " ++ v
  t :@ u -> do
    a@(tt, _) <- rec env t
    b@(uu, _) <- rec env u
    x <- newTV
    addConstraint (tt, uu :-> x)
    pure (x, a :@@ b)
  Lam args u -> do
    ts <- mapM (const newTV) args
    a@(tu, _) <- rec ((zip (filter (/= "_") args) $ zip ts $ repeat []) ++ env) u
    pure (foldr (:->) tu ts, AnnLam args a)
  Cas e as -> do
    aste@(te, _) <- rec env e
    x <- newTV
    astas <- forM as $ \(p, a) -> do
      let
        varsOf (t :@ u) = varsOf t ++ varsOf u
        varsOf (Var v) | isLower (head v) = [v]
        varsOf _ = []
      when (varsOf p /= nub (varsOf p)) $ bad "multiple binding in pattern"
      envp <- forM (varsOf p) $ \s -> (,) s . flip (,) [] <$> newTV
      -- TODO: Check p is a pattern.
      astp@(tp, _) <- rec (envp ++ env) p
      addConstraint (te, tp)
      asta@(ta, _) <- rec (envp ++ env) a
      addConstraint (x, ta)
      pure (astp, asta)
    pure (x, AnnCas aste astas)
  Let ds body -> do
    es <- forM (fst <$> ds) $ \s -> (,) s <$> newTV
    let envLet = (second (flip (,) []) <$> es) ++ env
    ts <- forM (snd <$> ds) $ rec envLet
    mapM_ addConstraint $ zip (snd <$> es) (fst <$> ts)
    body1@(t, _) <- rec envLet body
    pure (t, AnnLet (zip (fst <$> ds) ts) body1)
  Pack m n -> do  -- Only tuples are pre`Pack`ed.
    xs <- replicateM n newTV
    let r = foldl' (TApp) (TC "()") xs
    pure (foldr (:->) r xs, AnnPack m n)
-- TODO: Type classes for Call and Qual.
  Call c f -> case findExport c f of
    Left err -> bad err
    Right t -> flip (,) (AnnCall c f) . (TC "String" :->) .fst <$> instantiate (t, [])
  Qual c f -> case findExport c f of
    Left err -> bad err
    Right t -> flip (,) (AnnQual c f) . fst <$> instantiate (t, [])
  _ -> fail $ "BUG! unhandled: " ++ show ast
  where
    bad = Constraints . const . Left
    rec = gather findExport prelude

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

generalize :: [(String, Type)] -> Map String [String] -> AnnAst Type -> (QualType, Ast)
generalize soln ctx (t0, a0) = ((t, qs), dictSolve dsoln soln ast) where
  (t, qs) = runState (generalize' ctx $ typeSolve soln t0) []
  dsoln = zip qs $ ("#d" ++) . show <$> [(0::Int)..]
  ast = case deAnn a0 of
    Lam ss body -> Lam (dvars ++ ss) body
    body -> Lam dvars body
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
dictSolve dsoln soln ast = case ast of
  u :@ v  -> rec u :@ rec v
  Lam ss a -> Lam ss $ rec a
  Cas e alts -> Cas (rec e) $ (id *** rec) <$> alts

  Placeholder ">>=" t -> Var "snd" :@ rec (Placeholder "Monad" $ typeSolve soln t)
  Placeholder "pure" t -> Var "fst" :@ rec (Placeholder "Monad" $ typeSolve soln t)

  Placeholder "==" t -> rec $ Placeholder "Eq" $ typeSolve soln t
  Placeholder "save" t -> Var "fst" :@ rec (Placeholder "Save" $ typeSolve soln t)
  Placeholder "load" t -> Var "snd" :@ rec (Placeholder "Save" $ typeSolve soln t)
  Placeholder d t -> case typeSolve soln t of
    TV v -> Var $ fromJust $ lookup (d, v) dsoln
    u -> findInstance d u
  _       -> ast
  where
    rec = dictSolve dsoln soln
    findInstance "Eq" t = case t of
      TC "String"        -> Var "String-=="
      TC "Int"           -> Var "Int-=="
      TApp (TC "List") a -> Var "list_eq_instance" :@ rec (Placeholder "Eq" a)
      e -> error $ "BUG! no Eq for " ++ show e
    findInstance "Save" t = case t of
      TC "String" -> Pack 0 2 :@ Var "String-save" :@ Var "String-load"
      TC "Int" -> Pack 0 2 :@ Var "Int-save" :@ Var "Int-load"
      e -> error $ "BUG! no Save for " ++ show e
    findInstance "Monad" t = case t of
      TC "Maybe" -> Pack 0 2 :@ Var "maybe_pure" :@ Var "maybe_monad"
      TC "IO" -> Pack 0 2 :@ Var "io_pure" :@ Var "io_monad"
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

type Syscalls = Map String (Int, Type)

expandSyscalls :: Syscalls -> Ast -> Ast
expandSyscalls sys ast = case ast of
  t :@ u -> rec t :@ rec u
  Lam xs t -> Lam xs $ rec t
  Let xs t -> Let (second rec <$> xs) $ rec t
  Cas x as -> Cas (rec x) (second rec <$> as)
  Var s | Just (n, t) <- M.lookup s sys -> Var "#syscall" :@ I (argCount t) :@ I (fromIntegral n)
  _ -> ast
  where
    rec = expandSyscalls sys
    argCount (_ :-> u) = 1 + argCount u
    argCount _ = 0

hsToAst :: Syscalls -> String -> Either String [(String, Ast)]
hsToAst sys s = case parseDefs s of
  Left err -> Left $ "parse error: " ++ show err
  Right ds -> (second (expandSyscalls sys) <$>)
    . liftLambdas . (second snd <$>) <$>
    inferType (\_ _ -> Left "no exports") m (ds ++ hacks)
  where m = preludeMinimal `M.union` (first (const Nothing) <$> sys)

inferType
  :: (String -> String -> Either String Type)
  -> Globals
  -> [(String, Ast)]
  -> Either String [(String, (QualType, Ast))]
inferType findExport globs ds = foldM inferMutual [] $ map (map (\k -> (k, fromJust $ lookup k ds))) $ reverse $ scc (callees ds) $ fst <$> ds where
  -- inferMutual :: [(String, AnnAst Type)] -> [(String, Ast)] -> Either String [(String, AnnAst Type)]
  inferMutual acc grp = do
    (bs, ConState _ cs m) <- buildConstraints $ do
      ts <- mapM (gather findExport globs env) $ snd <$> grp
      when ("main" `elem` (fst <$> grp)) $ do
        r <- newTV
        addConstraint (TV "*main", TApp (TC "IO") r)
      mapM_ addConstraint $ zip tvs $ fst <$> ts
      pure ts
    (soln, ctx) <- runStateT (unify cs) m
    pure $ (++ acc) $ zip (fst <$> grp) $ generalize soln ctx <$> bs
    where
      buildConstraints (Constraints f) = f $ ConState 0 [] M.empty
      tvs = TV . ('*':) . fst <$> grp
      env = zip (fst <$> grp) (zip tvs $ repeat $ []) ++ map (second fst) acc

callees :: [(String, Ast)] -> String -> [String]
callees ds f = deps f (fromJust $ lookup f ds) where
  deps name body = case body of
    Lam ss t | name `notElem` ss -> rec t
    -- TODO: Look for shadowed function name in case and let statements.
    -- Or add deshadowing phase.
    Call "" v         -> [v]
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

freeV :: [(String, Ast)] -> [(String, AnnAst [String])]
freeV scs = map f scs where
  f (d, ast) = (d, g [] ast)
  g :: [String] -> Ast -> AnnAst [String]
  g cand (Lam ss a) = (vs \\ ss, AnnLam ss a1) where
    a1@(vs, _) = g (union cand ss) a
  g cand (x :@ y) = (fst x1 `union` fst y1, x1 :@@ y1) where
    x1 = g cand x
    y1 = g cand y
  g cand (Var v) | v `elem` cand = ([v], AnnVar v)
                 | otherwise     = ([],  AnnVar v)
  g cand (Cas x as) = (foldl' union (fst x1) $ fst <$> as1, AnnCas x1 $ snd <$> as1) where
    x1 = g cand x
    as1 = map h as
    h (p, e) = (vs1, (g [] p, (vs, e1))) where
      (vs, e1) = g (cand `union` caseVars p) e
      vs1 = vs \\ caseVars p
  g cand (Let ds e) = (fst e1 \\ binders, AnnLet ds1 e1) where
    e1 = g (cand `union` binders) e
    binders = fst <$> ds
    ds1 = map h ds
    h (s, x) = (s, g (cand `union` binders) x)
  g _    (I i) = ([], AnnI i)
  g _    (S s) = ([], AnnS s)
  g _    (Pack m n) = ([], AnnPack m n)
  g _    (Qual x y) = ([], AnnQual x y)
  g _    (Call x y) = ([], AnnCall x y)
  g _    (Placeholder x y) = ([], AnnPlaceholder x y)

caseVars :: Ast -> [String]
caseVars (Var v) = [v]
caseVars (x :@ y) = caseVars x `union` caseVars y
caseVars _ = []

liftLambdas :: [(String, Ast)] -> [(String, Ast)]
liftLambdas scs = existingDefs ++ newDefs where
  (existingDefs, (_, newDefs)) = runState (mapM f $ freeV scs) ([], [])
  f (s, (_, AnnLam args body)) = do
    modify $ first $ const [s]
    body1 <- g body
    pure (s, Lam args body1)
  f _ = error "bad top-level definition"
  genName :: State ([String], [(String, Ast)]) String
  genName = do
    (names, ys) <- get
    let
      n = head $ filter (`notElem` names) $
        (++ ('$':last names)) . show <$> [(0::Int)..]
    put (n:names, ys)
    pure n
  g (_, x :@@ y) = (:@) <$> g x <*> g y
  g (_, AnnLet ds t) = Let <$> mapM noLamb ds <*> g t where
    noLamb (name, (fvs, AnnLam ss body)) = do
      n <- genName
      body1 <- g body
      modify $ second ((n, Lam (fvs ++ ss) body1):)
      pure (name, foldl' (:@) (Var n) $ Var <$> fvs)
    noLamb (name, a) = (,) name <$> g a
  g (fvs, lam@(AnnLam _ _)) = do
    n <- genName
    g (fvs, AnnLet [(n, (fvs, lam))] ([n], AnnVar n))
  g (_, AnnCas expr as) =
    Cas <$> g expr <*> mapM (\(p, t) -> (,) <$> g p <*> g t) as
  g (_, ann) = pure $ deAnn ann

deAnn :: AnnAst' a -> Ast
deAnn (AnnS s) = S s
deAnn (AnnI i) = I i
deAnn (AnnVar v) = Var v
deAnn (AnnCall x y) = Call x y
deAnn (AnnQual x y) = Qual x y
deAnn (AnnPack x y) = Pack x y
deAnn (AnnPlaceholder x y) = Placeholder x y
deAnn (AnnCas (_, x) as) = Cas (deAnn x) $ (join (***) $ deAnn . snd) <$> as
deAnn (AnnLam as (_, x)) = Lam as $ deAnn x
deAnn (AnnLet as (_, x)) = Let (second (deAnn . snd) <$> as) $ deAnn x
deAnn ((_, x) :@@ (_, y)) = deAnn x :@ deAnn y
