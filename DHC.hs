{-# LANGUAGE CPP #-}
{-# LANGUAGE PackageImports #-}
module DHC
  ( parseModule, AstF(..), Ast(..), AstPlus(..), Type(..)
  , inferType, parseDefs, lexOffside
  , arityFromType, hsToAst, liftLambdas
  , HsProgram(..)
  ) where
import Control.Arrow
import Control.Monad
#ifdef __HASTE__
import "mtl" Control.Monad.State
#else
import Control.Monad.Reader
import Control.Monad.State
import qualified Data.ByteString.Char8 as B
import Data.ByteString.Short (ShortByteString, toShort)
#endif
import Data.Char
import Data.List
import qualified Data.Map.Strict as M
import Data.Map.Strict (Map)
import Data.Maybe
import Text.Parsec hiding (State)

import Ast
import Boost
import WasmOp (WasmType(..))

sbs :: String -> ShortByteString
#ifdef __HASTE__
sbs = id
type ShortByteString = String
#else
sbs = toShort . B.pack
#endif

data LayoutState = IndentAgain Int | LineStart | LineMiddle | AwaitBrace | Boilerplate deriving (Eq, Show)

-- | For some reason (too much backtracking + strict evaluation somewhere?)
-- quasiquotation parsing repeatedly visits the same quasiquoted code.
-- We use a cache so we only compile code once.
type QQCache = Map (String, String) (Either String String)
type QQuoter = String -> String -> Either String String
type QQMonad = State (QQuoter, QQCache)
type Parser = ParsecT String (LayoutState, [Int]) QQMonad

program :: Parser HsProgram
program = do
  filler
  r <- toplevels
  eof
  pure r

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

data HsProgram = HsProgram
  { supers :: [(String, Ast)]
  , datas :: [(String, (Maybe (Int, Int), Type))]
  , classes :: [(String, (Type, [(String, String)]))]
  } deriving Show

addSuper :: (String, Ast) -> HsProgram -> HsProgram
addSuper sc p = p { supers = sc:supers p }

addData :: [(String, (Maybe (Int, Int), Type))] -> HsProgram -> HsProgram
addData xs p = p { datas = xs ++ datas p }

addClass :: [(String, (Type, [(String, String)]))] -> HsProgram -> HsProgram
addClass xs p = p { classes = xs ++ classes p }

toplevels :: Parser HsProgram
toplevels = foldl' (flip ($)) (HsProgram [] [] []) <$> topDecls where
  topDecls = between (want "{") (want "}") (topDecl `sepBy` want ";")
  topDecl = dataDecl <|> classDecl <|> sc
  classDecl = do
    void $ want "class"
    s <- con
    t <- tyVar
    void $ want "where"
    ms <- between (want "{") (want "}") $ cDecl `sepBy` want ";"
    pure $ addClass $ second (flip (,) [(s, t)]) <$> ms
  cDecl = do
    v <- var
    void $ want "::"
    t <- typeExpr
    pure (v, t)
  dataDecl = do
    void $ want "data"
    s <- con
    args <- many tyVar
    void $ want "="
    let
      t = foldl' TApp (TC s) $ GV <$> args
      typeCon = do
        c <- con
        ts <- many atype
        pure (c, foldr (:->) t ts)
    typeCons <- typeCon `sepBy` want "|"
    pure $ addData [(c, (Just (i, arityFromType typ), typ))
      | (i, (c, typ)) <- zip [0..] typeCons]
  typeExpr = foldr1 (:->) <$> btype `sepBy` want "->"
  btype = foldl1' TApp <$> many1 atype
  -- Unsupported: [] (->) (,{,}) constructors.
  atype = (TC <$> con)
    <|> (GV <$> tyVar)
    <|> (TApp (TC "[]") <$> between (want "[") (want "]") typeExpr)
    <|> (parenType <$> between (want "(") (want ")") (typeExpr `sepBy` want ","))
  parenType []  = TC "()"
  parenType [x] = x
  parenType xs  = foldr1 TApp $ TC "()":xs
  sc = try (do
    (fun:args) <- scOp <|> many1 var
    void $ want "="
    addSuper . (,) fun . Ast . Lam args <$> expr) <|> pure id
  scOp = try $ do
    l <- var
    op <- varSym
    r <- var
    pure [op, l, r]
  expr = caseExpr <|> letExpr <|> doExpr <|> bin 0 False
  bin 10 _ = molecule
  bin prec isR = rec False =<< bin (prec + 1) False where
    rec isL m = (try $ do
      o <- varSym <|> between (want "`") (want "`") var
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
    s <- var
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
  -- TODO: Introduce patterns to deal with _.
  lambda = fmap Ast $ Lam <$> between (want "\\") (want "->") (many1 (var <|> want "_")) <*> expr
  molecule = lambda <|> foldl1' ((Ast .) . (:@)) <$> many1 atom
  atom = tup <|> qvar
    <|> (Ast . Var <$> want "_")
    <|> (Ast . Var <$> var)
    <|> (Ast . Var <$> con)
    <|> num <|> str <|> lis <|> enumLis
  tup = try $ do
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
  num = try $ do
    (t, s) <- tok
    when (t /= LexNumber) $ fail ""
    pure $ Ast $ I $ read s
  str = try $ do
    (t, s) <- tok
    when (t /= LexString) $ fail ""
    pure $ Ast $ S $ sbs s
  con = try $ do
    (t, s) <- tok
    when (t /= LexCon) $ fail ""
    pure s
  tyVar = varId

varId :: Parser String
varId = try $ do
  (t, s) <- tok
  when (t /= LexVar) $ fail ""
  pure s

varSym :: Parser String
varSym = do
  (t, s) <- tok
  when (t /= LexVarSym) $ fail ""
  pure s

var :: Parser String
var = varId <|> (try $ between (want "(") (want ")") varSym)

reservedIds :: [String]
reservedIds = words "class data default deriving do else foreign if import in infix infixl infixr instance let module newtype of then type where _"

reservedOps :: [String]
reservedOps = ["..", "::", "=", "|", "<-", "->", "=>"]

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

data LexemeType = LexString | LexNumber | LexReserved | LexVar | LexCon | LexSpecial | LexVarSym | LexQual | LexEOF deriving (Eq, Show)
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
  r <- oxford <|> symbol <|> qId <|> num <|> special <|> str
  pure r
  where
  oxford = do
    q <- try $ between (char '[') (char '|') $ many alphaNum
    s <- oxfordClose <|> more
    (f, cache) <- get
    answer <- case M.lookup (q, s) cache of
      Nothing -> do
        let x = f q s
        put (f, M.insert (q, s) x cache)
        pure x
      Just x -> pure x
    either (fail . ("quasiquotation: " ++)) (pure . (,) LexString) answer
    where
    oxfordClose = try (string "|]") >> pure ""
    more = do
      s <- innerOxford <|> (pure <$> anyChar)
      (s ++) <$> (oxfordClose <|> more)
    innerOxford = do
      q <- try $ between (char '[') (char '|') $ many alphaNum
      s <- oxfordClose <|> more
      pure $ '[':q ++ ('|':s) ++ "|]"
  lowId = do
    s <- (:) <$> (lower <|> char '_') <*> many (alphaNum <|> oneOf "_'")
    when (s `elem` ["let", "where", "do", "of"]) $ do
      (_, is) <- getState
      putState (AwaitBrace, is)
    pure (if s `elem` reservedIds then LexReserved else LexVar, s)
  uppId = do
    s <- (:) <$> upper <*> many (alphaNum <|> oneOf "_'")
    pure (LexCon, s)
  qId = do
    r@(_, m) <- lowId <|> uppId
    (try $ do
      void $ char '.'
      (_, v) <- lowId <|> uppId
      pure (LexQual, m ++ '.':v)) <|> pure r
  num = do
    s <- many1 digit
    pure (LexNumber, s)
  special = (,) LexSpecial <$> foldl1' (<|>) (string . pure <$> "(),;[]`{}")
  symbol = do
    s <- many1 (oneOf "!#$%&*+./<=>?@\\^|-~:")
    pure (if s `elem` reservedOps then LexReserved else LexVarSym, s)
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
  { wdecls :: [String]
  , stores :: [String]
  , defs :: HsProgram
  , funTypes :: [(String, QualType)]
  } deriving Show

contract :: Parser AstPlus
contract = do
  ws <- option [] $ try $ want "wdecl" >>
    (between (want "(") (want ")") $ var `sepBy` want ",")
  ps <- option [] $ try $ want "store" >>
    (between (want "(") (want ")") $ var `sepBy` want ",")
  putState (AwaitBrace, [])
  p <- toplevels
  when (isNothing $ mapM (`lookup` supers p) ws) $ fail "bad wdecls"
  pure $ AstPlus ws ps p []

qParse :: Parser a
  -> (LayoutState, [Int])
  -> String
  -> String
  -> Either ParseError a
qParse a b c d = evalState (runParserT a b c d) (justHere, M.empty)

justHere :: QQuoter
justHere "here" s = Right s
justHere _ _ = Left "bad scheme"

lexOffside :: String -> Either ParseError [String]
lexOffside = fmap (fmap snd) <$> qParse tokUntilEOF (AwaitBrace, []) "" where
  tokUntilEOF = do
    t <- tok
    case fst t of
      LexEOF -> pure []
      _ -> (t:) <$> tokUntilEOF

parseDefs :: String -> Either ParseError HsProgram
parseDefs = qParse program (AwaitBrace, []) ""

parseModule :: String -> Either ParseError AstPlus
parseModule = qParse contract (Boilerplate, []) ""

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
  :: Globals
  -> [(String, QualType)]
  -> Ast
  -> Constraints (AAst Type)
gather globs env (Ast ast) = case ast of
  I i -> pure $ AAst (TC "Int") $ I i
  S s -> pure $ AAst (TC "String") $ S s
  Pack m n -> do  -- Only tuples are pre`Pack`ed.
    xs <- replicateM n newTV
    let r = foldr1 TApp $ TC "()":xs
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
      Nothing -> case M.lookup v globs of
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
  _ -> fail $ "BUG! unhandled: " ++ show ast
  where
    rec = gather globs
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

generalize
  :: Map String Type      -- Solution found through type unification.
  -> Map String [String]  -- Context for qualified types.
  -> (String, AAst Type)
  -> (String, (QualType, Ast))
generalize soln ctx (fun, a0@(AAst t0 _)) = (fun, (qt, a1)) where
  qt@(_, qs) = runState (generalize' ctx $ typeSolve soln t0) []
  -- TODO: Here, and elsewhere: need to sort qs?
  dsoln = zip qs $ ("#d" ++) . show <$> [(0::Int)..]
  -- TODO: May be useful to preserve type annotations?
  a1 = dictSolve dsoln soln ast
  dvars = snd <$> dsoln
  ast = case deAnn a0 of
    Ast (Lam ss body) -> Ast $ Lam (dvars ++ ss) $ expandFun body
    body -> Ast $ Lam dvars $ expandFun body
  -- TODO: Take shadowing into account.
  expandFun
    | null dvars = id
    | otherwise  = ffix $ \h (Ast a) -> Ast $ case a of
      Var v | v == fun -> foldl' (\x d -> (Ast x :@ Ast (Var d))) a dvars
      _ -> h a

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

methods :: Map String (Type, [(String, String)])
methods = M.fromList
  [ ("==", (a :-> a :-> TC "Bool", [("Eq", "a")]))
  , (">>=", (TApp m a :-> (a :-> TApp m b)  :-> TApp m b, [("Monad", "m")]))
  , ("pure", (a :-> TApp m a, [("Monad", "m")]))
  -- Generates call_indirect ops.
  , ("callSlot", (TC "I32" :-> a :-> TApp (TC "IO") (TC "()"), [("Message", "a")]))
  , ("set", (TApp (TC "Storage") a :-> a :-> io (TC "()"), [("Store", "a")]))
  , ("get", (TApp (TC "Storage") a :-> io a, [("Store", "a")]))
  ] where
    a = GV "a"
    b = GV "b"
    m = GV "m"
    io = TApp (TC "IO")

getBasic :: String -> Maybe WasmType
getBasic "Databuf" = Just I32
getBasic "Actor" = Just I32
getBasic "Port" = Just I32
getBasic "I32" = Just I32
getBasic "Int" = Just I64
getBasic _ = Nothing

basicsFromTuple :: Type -> [WasmType]
basicsFromTuple (TC "()") = []
basicsFromTuple (TC s) = [fromMaybe (error $ "bad basic: " ++ s) $ getBasic s]
basicsFromTuple (TApp (TC "()") t) = f t where
  f (TC s `TApp` rest) = fromJust (getBasic s):f rest
  f (TC s) = [fromJust $ getBasic s]
  f _ = error $ "expected Message: " ++ show t
basicsFromTuple t = error $ "expected Message: " ++ show t

dictSolve :: [((String, String), String)] -> Map String Type -> Ast -> Ast
dictSolve dsoln soln (Ast ast) = case ast of
  u :@ v  -> Ast $ rec u :@ rec v
  Lam ss a -> Ast $ Lam ss $ rec a
  Cas e alts -> Ast $ Cas (rec e) $ (id *** rec) <$> alts
  Placeholder ">>=" t -> aVar "snd" @@ rec (Ast $ Placeholder "Monad" $ typeSolve soln t)
  Placeholder "pure" t -> aVar "fst" @@ rec (Ast $ Placeholder "Monad" $ typeSolve soln t)
  Placeholder "==" t -> rec $ Ast $ Placeholder "Eq" $ typeSolve soln t
  Placeholder "callSlot" t -> rec $ Ast $ Placeholder "Message" $ typeSolve soln t
  --   set x y = #seti32 x (toAny y)
  Placeholder "set" t -> Ast $ Lam ["x", "y"] $ aVar "#seti32" @@ aVar "x" @@ (aVar "fst" @@ rec (Ast $ Placeholder "Store" $ typeSolve soln t) @@ aVar "y")
  --   get x = #geti32 x >>= pure . fromAny
  Placeholder "get" t -> Ast $ Lam ["x"] $ aVar "io_monad" @@ (aVar "#geti32" @@ aVar "x") @@ (aVar "." @@ aVar "io_pure" @@ (aVar "snd" @@ rec (Ast $ Placeholder "Store" $ typeSolve soln t)))
  Placeholder d t -> case typeSolve soln t of
    TV v -> Ast $ Var $ fromMaybe (error $ "unsolvable: " ++ show (d, v)) $ lookup (d, v) dsoln
    u -> findInstance d u
  _       -> Ast ast
  where
    aVar = Ast . Var
    infixl 5 @@
    x @@ y = Ast $ x :@ y
    rec = dictSolve dsoln soln
    findInstance "Message" t = Ast $ CallSlot $ basicsFromTuple t
    findInstance "Eq" t = case t of
      TC "String"        -> aVar "String-=="
      TC "Int"           -> aVar "Int-=="
      TApp (TC "[]") a -> aVar "list_eq_instance" @@ rec (Ast $ Placeholder "Eq" a)
      e -> error $ "BUG! no Eq for " ++ show e
    findInstance "Monad" t = case t of
      TC "Maybe" -> Ast (Pack 0 2) @@ aVar "maybe_pure" @@ aVar "maybe_monad"
      TC "IO" -> Ast (Pack 0 2) @@ aVar "io_pure" @@ aVar "io_monad"
      e -> error $ "BUG! no Monad for " ++ show e
    findInstance "Store" t = case t of
      TC "Databuf" -> Ast (Pack 0 2) @@ aVar "Databuf-toAny" @@ aVar "Databuf-fromAny"
      TC "Port" -> Ast (Pack 0 2) @@ aVar "Port-toAny" @@ aVar "Port-fromAny"
      TC "Actor" -> Ast (Pack 0 2) @@ aVar "Actor-toAny" @@ aVar "Actor-fromAny"
      TC "Int" -> Ast (Pack 0 2) @@ aVar "Int-toAny" @@ aVar "Int-fromAny"
      TApp (TC "[]") a -> let
        ltai = aVar "list_to_any_instance" @@ rec (Ast $ Placeholder "Store" a)
        lfai = aVar "list_from_any_instance" @@ rec (Ast $ Placeholder "Store" a)
        in Ast (Pack 0 2) @@ ltai @@ lfai
      TApp (TC "()") (TApp a b) -> let
        ptai = aVar "pair_to_any_instance" @@ rec (Ast $ Placeholder "Store" a) @@ rec (Ast $ Placeholder "Store" b)
        pfai = aVar "pair_from_any_instance" @@ rec (Ast $ Placeholder "Store" a) @@ rec (Ast $ Placeholder "Store" b)
        in Ast (Pack 0 2) @@ ptai @@ pfai
      e -> error $ "BUG! no Store for " ++ show e
    findInstance d t = error $ "BUG! bad class: " ++ show (d, t)

typeSolve :: Map String Type -> Type -> Type
typeSolve soln t = case t of
  TApp a b      -> rec a `TApp` rec b
  a :-> b       -> rec a :-> rec b
  TV x          -> fromMaybe t $ M.lookup x soln
  _             -> t
  where rec = typeSolve soln

-- | The `propagateClasses` and `propagateClassTyCon` functions of
-- "Implementing type classes".
propagate :: [String] -> Type -> Either String [(String, [String])]
propagate [] _ = Right []
propagate cs (TV y) = Right [(y, cs)]
propagate cs t = concat <$> mapM propagateTyCon cs where
  propagateTyCon "Eq" = case t of
    TC "Int" -> Right []
    TC "String" -> Right []
    TApp (TC "[]") a -> propagate ["Eq"] a
    _ -> Left $ "no Eq instance: " ++ show t
  propagateTyCon "Monad" = case t of
    TC "Maybe" -> Right []
    TC "IO" -> Right []
    _ -> Left $ "no Monad instance: " ++ show t
  propagateTyCon "Store" = case t of
    TApp (TC "()") (TApp a b) -> (++) <$> propagate ["Store"] a <*> propagate ["Store"] b
    TApp (TC "[]") a -> propagate ["Store"] a
    TC "Databuf" -> Right []
    TC "Actor" -> Right []
    TC "Port" -> Right []
    TC "Int" -> Right []
    _ -> Left $ "no Store instance: " ++ show t
  propagateTyCon "Message" =
    concat <$> (mapM (propagate ["MessageItem"]) =<< listFromTupleType t)
  propagateTyCon "MessageItem" = case t of
    TC s -> case getBasic s of
      Nothing -> Left $ "no Message instance: " ++ s
      Just _ -> Right []
    _ -> Left $ "no Message instance: " ++ show t
  propagateTyCon c = error $ "TODO: " ++ c
  listFromTupleType ty = case ty of
    TC "()" -> Right []
    TC _ -> Right [ty]
    TV _ -> Right [ty]
    TApp (TC "()") rest -> weirdList rest
    _ -> Left $ "want tuple: " ++ show ty
    where
    -- Tuples are represented oddly in our Type data structure.
    weirdList tup = case tup of
      TC _ -> Right [tup]
      TV _ -> Right [tup]
      TApp h@(TC _) rest -> (h:) <$> weirdList rest
      TApp h@(TV _) rest -> (h:) <$> weirdList rest
      _ -> Left $ "want tuple: " ++ show tup

unify :: [(Type, Type)] -> Map String [String] -> Either String (Map String Type, Map String [String])
unify constraints ctx = execStateT (uni constraints) (M.empty, ctx)
  where
  uni :: [(Type, Type)] -> StateT (Map String Type, Map String [String]) (Either String) ()
  uni [] = do
    (tm, qm) <- get
    as <- forM (M.keys tm) $ follow . TV
    put (M.fromList $ zip (M.keys tm) as, qm)
  uni ((GV _, _):_) = nope "BUG! generalized variable in constraint"
  uni ((_, GV _):_) = nope "BUG! generalized variable in constraint"
  uni ((lhs, rhs):cs) = do
    z <- (,) <$> follow lhs <*> follow rhs
    case z of
      (s, t) | s == t -> uni cs
      (TV x, TV y) -> do
        when (x /= y) $ do
          (tm, qm) <- get
          -- (Ideally should union by rank.)
          put (M.insert x (TV y) tm, case M.lookup x qm of
            Just q -> M.insert y q $ M.delete x qm
            _ -> qm)
        uni cs
      (TV x, t) -> do
        -- TODO: Test infinite type detection.
        if x `elem` freeTV t then nope $ "infinite: " ++ x ++ " = " ++ show t
        else do
          -- The `instantiateTyvar` function of "Implementing type classes".
          (_, qm) <- get
          -- For example, Eq [a] propagates to Eq a, which we record.
          either nope addQuals $ propagate (fromMaybe [] $ M.lookup x qm) t
          modify' $ first $ M.insert x t
          uni cs
      (s, t@(TV _)) -> uni $ (t, s):cs
      (TApp s1 s2, TApp t1 t2) -> uni $ (s1, t1):(s2, t2):cs
      (s1 :-> s2, t1 :-> t2) -> uni ((s1, t1):(s2, t2):cs)
      (s, t) -> nope $ "mismatch: " ++ show s ++ " /= " ++ show t
  addQuals = modify' . second . M.unionWith union . M.fromList
  nope = lift . Left
  -- Galler-Fischer-esque Data.Map (path compression).
  follow :: Type -> StateT (Map String Type, a) (Either String) Type
  follow t = case t of
    TApp a b -> TApp <$> follow a <*> follow b
    a :-> b  -> (:->) <$> follow a <*> follow b
    TV x     -> do
      (tm, qm) <- get
      case M.lookup x tm of
        Just u -> do
          z <- follow u
          put (M.insert x z tm, qm)
          pure z
        Nothing -> pure $ TV x
    _        -> pure t
  freeTV :: Type -> [String]
  freeTV t = case t of
    TApp a b -> freeTV a ++ freeTV b
    a :-> b  -> freeTV a ++ freeTV b
    TV tv    -> [tv]
    _        -> []

arityFromType :: Type -> Int
arityFromType = f 0 where
  f acc (_ :-> r) = f (acc + 1) r
  f acc _ = acc

boostTypes :: Boost -> Map String (Maybe (Int, Int), Type)
boostTypes b = M.fromList $ second (((,) Nothing) . fst) <$> boostHs b

hsToAst :: Boost -> QQuoter -> String -> Either String AstPlus
hsToAst boost qq prog = do
  a@(AstPlus _ _ ds _) <- showErr $ evalState (runParserT contract (Boilerplate, []) "" prog) (qq, M.empty)
  (preStorageInferred, storageCons) <- inferType (genTypes (datas ds) $ stores a) (wdecls a) (supers ds ++ supers preludeDefs)
  let
    inferred = constrainStorage storageCons preStorageInferred
    subbedDefs = (second expandCase <$>) . liftLambdas . (second snd <$>) $ inferred
    types = second fst <$> inferred
  pure a { defs = (defs a) { supers = subbedDefs }, funTypes = types }
  where
    -- List notation is a special case in Haskell.
    -- This is "data [a] = [] | a : [a]" in spirit.
    listPresets = M.fromList
      [ ("[]", (Just (0, 0), TApp (TC "[]") a))
      , (":",  (Just (1, 2), a :-> TApp (TC "[]") a :-> TApp (TC "[]") a))
      ] where a = GV "a"
    genTypes dataDecls ps = listPresets
      `M.union` M.fromList (datas preludeDefs)
      `M.union` M.fromList dataDecls
      `M.union` boostTypes boost
      `M.union` (M.fromList $ storeTypeConstraint <$> ps)
    Right preludeDefs = parseDefs $ boostPrelude boost
    showErr = either (Left . show) Right
    storeTypeConstraint s = (s, (Nothing, TC "Storage" `TApp` TV ('@':s)))

constrainStorage :: Map String Type -> [(String, (QualType, Ast))] -> [(String, (QualType, Ast))]
constrainStorage cons ds = second (first (first rewriteType)) <$> ds where
  rewriteType (GV ('@':x)) = case typeSolve cons $ TV ('@':x) of
    TC t -> TC t
    _    -> TC "String"
  rewriteType (t :-> u) = rec t :-> rec u
  rewriteType (TApp t u) = TApp (rec t) (rec u)
  rewriteType t = t
  rec = rewriteType

inferType
  :: Globals
  -> [String]  -- wdecl functions.
  -> [(String, Ast)]  -- Supercombinator definitions.
  -- Returns types of definitions and stores.
  -> Either String ([(String, (QualType, Ast))], Map String Type)
inferType globs ws ds = foldM inferMutual ([], M.empty) $ map (map (\k -> (k, fromJust $ lookup k ds))) sortedDefs where
  -- Groups of definitions, sorted in the order we should infer their types.
  sortedDefs = reverse $ scc (callees ds) $ fst <$> ds
  inferMutual :: ([(String, (QualType, Ast))], Map String Type) -> [(String, Ast)] -> Either String ([(String, (QualType, Ast))], Map String Type)
  inferMutual (acc, accStorage) grp = do
    (typedAsts, ConState _ cs m) <- buildConstraints $ forM grp $ \(s, d) -> do
      t <- gather globs env d
      addConstraint (TV $ '*':s, annOf t)
      when (s `elem` ws) $
        addConstraint (retType $ annOf t, TApp (TC "IO") $ TC "()")
      pure (s, t)
    (soln, ctx) <- unify cs m
    let storageCons = M.filterWithKey (\k _ -> head k == '@') soln
    -- TODO: Look for conflicting storage constraints.
    pure ((++ acc) $ generalize soln ctx <$> typedAsts, accStorage `M.union` storageCons)
    where
      retType (_ :-> a) = retType a
      retType r = r
      annOf (AAst a _) = a
      buildConstraints (Constraints f) = f $ ConState 0 [] M.empty
      tvs = TV . ('*':) . fst <$> grp
      env = zip (fst <$> grp) (zip tvs $ repeat $ []) ++ map (second fst) acc

-- TODO: For finding strongly-connected components, there's no need to find
-- all dependencies. If a node has already been processed, we should avoid
-- finding all its dependencies again. We can do this by passing in a list of
-- nodes that have already been explored.
callees :: [(String, Ast)] -> String -> [String]
callees ds s = snd $ execState (go s) ([], []) where
  go :: String -> State ([String], [String]) ()
  go f = do
    (env, acc) <- get
    when (not $ elem f env || elem f acc || M.member f methods) $ case lookup f ds of
      -- TODO: If we knew the primitives (functions implemented in wasm, such
      -- as `*`), then we could detect out-of-scope identifiers here.
      Nothing -> pure ()  -- error $ "not in scope: " ++ f
      Just d -> do
        put (env, f:acc)
        ast d
  ast (Ast d) = case d of
    x :@ y -> ast x >> ast y
    Lam ss t -> do
      env <- gets fst
      modify $ first (ss ++)
      ast t
      modify $ first (const env)
    Var v -> go v
    Cas x as -> do
      ast x
      forM_ as $ \(Ast p, e) -> do
        env <- gets fst
        modify $ first (caseVars p ++)
        ast e
        modify $ first (const env)
    Let as x -> do
      env <- gets fst
      modify $ first ((fst <$> as) ++)
      mapM_ ast $ snd <$> as
      ast x
      modify $ first (const env)
    _ -> pure ()

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
  g _ x = ffix (\h (Ast ast) -> AAst [] $ h ast) $ Ast x

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

    -- TODO: Call `fromApList` only in last case alternative.
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
