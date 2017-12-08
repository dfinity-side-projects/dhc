{-# LANGUAGE DeriveGeneric #-}
{-# LANGUAGE PackageImports #-}
module DHC (parseContract, Ast(..), Type(..), inferType,
  preludeMinimal, compileMinimal, liftLambdas) where

import Control.Arrow
import Control.DeepSeq (NFData(..))
import Control.Monad
import "mtl" Control.Monad.State
import Data.Binary (Binary)
import Data.ByteString.Short (ShortByteString, pack)
import Data.ByteString.Internal (c2w)
import Data.Char
import Data.Int
import Data.List
import qualified Data.Map.Strict as M
import Data.Map.Strict (Map)
import Data.Maybe
import GHC.Generics (Generic)
import Text.ParserCombinators.Parsec hiding (State)

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

program :: Parser [(String, Ast)]
program = do
  filler
  defs <- supercombinators
  eof
  pure defs

supercombinators :: Parser [(String, Ast)]
supercombinators = sc `sepBy` want ";" where
  sc = do
    (fun:args) <- many1 varStr
    void $ want "="
    (,) fun . Lam args <$> expr
  expr = caseExpr <|> letExpr <|>
    molecule `chainr1` chop "." `chainr1` chop "^"
      `chainl1` chop "*/" `chainl1` chop "+-"
      `chainr1` sop [":", "++"]
      `chainl1` sop ["<", ">", "<=", ">=", "==", "/="]
      `chainl1` sop ["&&"]
      `chainl1` sop ["||"]
      `chainl1` sop [">>", ">>="]
  letDefn = do
    s <- varStr
    void $ want "="
    ast <- expr
    pure (s, ast)
  letExpr = do
    ds <- between (want "let") (want "in") $
      between (want "{") (want "}") $ letDefn `sepBy` want ";"
    Let ds <$> expr
  caseExpr = do
    x <- between (want "case") (want "of") expr
    as <- alt `sepBy` want ";"
    pure $ Cas x as
  lambda = Lam <$> between (want "\\") (want "->") (many1 varStr) <*> expr
  alt = do
    p <- expr  -- TODO: Restrict to patterns.
    void $ want "->"
    x <- expr
    pure $ (p, x)
  chop xs = try $ do
    s <- foldl1' (<|>) $ map (want . pure) xs
    pure $ \x y -> Var s :@ x :@ y
  sop xs = try $ do
    s <- foldl1' (<|>) $ want <$> xs
    pure $ \x y -> Var s :@ x :@ y
  molecule = lambda <|> foldl1' (:@) <$> many1 atom
  atom = preOp <|> tup <|> call <|> qvar <|> var <|> num <|> str
    <|> lis <|> enumLis
  preOp = try $ Var <$> between (want "(") (want ")") opTok
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
  qvar = try $ do
    s <- many1 alphaNum
    void $ char '.'
    v <- varStr
    pure $ Qual s v
  call = try $ do
    void $ want "call"
    s <- (try $ do
      q <- many1 alphaNum
      void $ char '.'
      pure q) <|> pure ""
    v <- varStr
    pure $ Call s v
  num = try $ do
    s <- tok
    unless (all isDigit s) $ fail ""
    pure $ I $ read s
  str = do
    s <- try <$> between (char '"') (char '"') $ S . pack <$> many rune
    filler
    pure s
  rune = c2w <$> ((char '\\' >> oneOf "\\\"") <|> noneOf "\"")

varStr :: Parser String
varStr = try $ do
  s@(h:_) <- tok
  when (not (isLetter h) || s `elem` words "case of let where do in _ call") $ fail ""
  pure s

want :: String -> Parser String
want t = try $ do
  s <- tok
  unless (s == t) $ fail $ "expected " ++ t
  pure s

opTok :: Parser String
opTok = do
  s <- many1 (oneOf "\\:!+-/*^><=$.&|")
  filler
  pure s

tok :: Parser String
tok = opTok <|> do
  s <- many1 (alphaNum <|> char '_') <|>
       foldl1' (<|>) (string . pure <$> ";()[]{},")
  filler
  pure s

filler :: Parser ()
filler = void $ many $ many1 space <|>
  (between (try $ string "--") (char '\n') $ many $ noneOf "\n")

contract :: Parser ([String], [String], [(String, Ast)])
contract = do
  filler
  es <- option [] $ try $ want "contract" >>
    (between (want "(") (want ")") $ varStr `sepBy` want ",")
  ms <- option [] $ try $ want "storage" >>
    (between (want "(") (want ")") $ varStr `sepBy` want ",")
  ds <- supercombinators
  eof
  when (isNothing $ mapM (`lookup` ds) es) $ fail "bad exports"
  pure (es, ms, ds)

parseDefs :: String -> Either ParseError [(String, Ast)]
parseDefs = parse program ""

parseContract :: String -> Either ParseError ([String], [String], [(String, Ast)])
parseContract = parse contract "" where

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

type Globals = Map String (Maybe Ast, Type)

-- | Gathers constraints.
-- Replaces '==' with Placeholder.
-- Replaces data constructors with Pack.
gather
  :: (String -> String -> Either String Type)
  -> Globals
  -> [(String, Type)]
  -> Ast
  -> Constraints (Ast, Type)
gather findExport prelude env ast = case ast of
  I _ -> pure (ast, TC "Int")
  S _ -> pure (ast, TC "String")
  Var v -> case lookup v env of
    Just t  -> if v `M.member` prelude then bad $ "ambiguous: " ++ v
      else (,) ast <$> instantiate t
    Nothing -> if v == "==" then do
        TV x <- newTV
        addContext "Eq" x
        pure (Placeholder "==" $ TV x, TV x :-> TV x :-> TC "Bool")
      else case M.lookup v prelude of
        Just (ma, t) -> (,) (fromMaybe ast ma) <$> instantiate t
        Nothing      -> bad $ "undefined: " ++ v
  t :@ u -> do
    (a, tt) <- rec env t
    (b, uu) <- rec env u
    x <- newTV
    addConstraint (tt, uu :-> x)
    pure (a :@ b, x)
  Call c f -> case findExport c f of
    Left err -> bad err
    Right t -> (,) ast . (TC "String" :->) <$> instantiate t
  Lam args u -> do
    ts <- mapM (const newTV) args
    (a, tu) <- rec ((zip args ts) ++ env) u
    pure (Lam args a, foldr (:->) tu ts)
  Cas e as -> do
    (aste, te) <- rec env e
    x <- newTV
    astas <- forM as $ \(p, a) -> do
      let
        varsOf (t :@ u) = varsOf t ++ varsOf u
        varsOf (Var v) | isLower (head v) = [v]
        varsOf _ = []
      when (varsOf p /= nub (varsOf p)) $ bad "multiple binding in pattern"
      envp <- forM (varsOf p) $ \s -> (,) s <$> newTV
      -- TODO: Check p is a pattern.
      (astp, tp) <- rec (envp ++ env) p
      addConstraint (te, tp)
      (asta, ta) <- rec (envp ++ env) a
      addConstraint (x, ta)
      pure (astp, asta)
    pure (Cas aste astas, x)
  Let ds body -> do
    es <- forM (fst <$> ds) $ \s -> (,) s <$> newTV
    ts <- forM (snd <$> ds) $ rec (es ++ env)
    mapM_ addConstraint $ zip (snd <$> es) (snd <$> ts)
    (body1, t) <- rec (es ++ env) body
    pure (Let (zip (fst <$> ds) (fst <$> ts)) body1, t)
  Pack _ n -> do  -- Only tuples are pre`Pack`ed.
    xs <- replicateM n newTV
    let r = foldl' (TApp) (TC "()") xs
    pure (ast, foldr (:->) r xs)
  Qual c f -> case findExport c f of
    Left err -> bad err
    Right t -> (,) ast <$> instantiate t
  _ -> fail $ "BUG! unhandled: " ++ show ast
  where
    bad = Constraints . const . Left
    rec = gather findExport prelude
    instantiate ty = do  -- Instantiate generalized variables.
      let
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
      snd <$> f [] ty

generalize :: [String] -> Type -> Type
generalize fvs ty = case ty of
  TV s | s `notElem` fvs -> GV s
  u :-> v  -> generalize fvs u :-> generalize fvs v
  TApp u v -> generalize fvs u `TApp` generalize fvs v
  _        -> ty

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

typeClass :: String -> Type -> Map String [String] -> Either String (Map String [String])
typeClass x (TV y) m = Right $
  M.insertWith union y (fromMaybe [] $ M.lookup x m) m
typeClass x t m
  | Just ["Eq"] <- M.lookup x m = if t == TC "Int" || t == TC "String"
    then Right m
    else Left $ "no Eq instance: " ++ show t
  | otherwise = Right m

fillPlaceholders :: [(String, Type)] -> Ast -> Ast
fillPlaceholders soln ast = case ast of
  u :@ v  -> rec u :@ rec v
  Lam ss a -> Lam ss $ rec a
  Cas e alts -> Cas (rec e) $ (id *** rec) <$> alts
  Placeholder "==" t -> case typeSolve soln t of
    TC "String" -> Var "String-=="
    TC "Int"    -> Var "Int-=="
    e -> error $ "want String or Int; got " ++ show e
  _       -> ast
  where rec = fillPlaceholders soln

typeSolve :: [(String, Type)] -> Type -> Type
typeSolve soln t = foldl' (flip subst) t soln

-- TODO: Apply substitutions for friendlier messages.
unify :: [(Type, Type)] -> Map String [String] -> Either String [(String, Type)]
unify [] _ = Right []
unify ((GV _, _):_) _ = Left "BUG! generalized variable in constraint"
unify ((_, GV _):_) _ = Left "BUG! generalized variable in constraint"
unify ((s, t):cs) m | s == t = unify cs m
unify ((TV x, t):cs) m
  | x `elem` freeTV t = Left $ "infinite: " ++ x ++ " = " ++ show t
  | otherwise         = typeClass x t m >>= (\m1 -> ((x, t):) <$> unify (join (***) (subst (x, t)) <$> cs) m1)
unify ((s, t@(TV _)):cs) m = unify ((t, s):cs) m
unify ((TApp s1 s2, TApp t1 t2):cs) m = unify ((s1, t1):(s2, t2):cs) m
unify (( s1 :-> s2, t1 :-> t2):cs)  m = unify ((s1, t1):(s2, t2):cs) m
unify ((s, t):_) _    = Left $ "mismatch: " ++ show s ++ " /= " ++ show t

preludeMinimal :: Map String (Maybe Ast, Type)
preludeMinimal = M.fromList $ (second ((,) Nothing) <$>
  [ ("+", TC "Int" :-> TC "Int" :-> TC "Int")
  , ("-", TC "Int" :-> TC "Int" :-> TC "Int")
  , ("*", TC "Int" :-> TC "Int" :-> TC "Int")
  , ("div", TC "Int" :-> TC "Int" :-> TC "Int")
  , ("mod", TC "Int" :-> TC "Int" :-> TC "Int")
  , ("<", TC "Int" :-> TC "Int" :-> TC "Bool")
  , (">", TC "Int" :-> TC "Int" :-> TC "Bool")
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
    jp = (Just .) . Pack
    a = GV "a"
    b = GV "b"

compileMinimal :: String -> Either String [(String, Ast)]
compileMinimal s = case parseDefs s of
  Left err -> Left $ "parse error: " ++ show err
  Right ds -> liftLambdas . (second fst <$>) <$>
    inferType (\_ _ -> Left "no exports") preludeMinimal ds

inferType
  :: (String -> String -> Either String Type)
  -> Globals
  -> [(String, Ast)]
  -> Either String [(String, (Ast, Type))]
inferType findExport globs ds = foldM inferMutual [] $ map (map (\k -> (k, fromJust $ lookup k ds))) $ reverse $ scc (callees ds) $ fst <$> ds where
  inferMutual :: [(String, (Ast, Type))] -> [(String, Ast)] -> Either String [(String, (Ast, Type))]
  inferMutual acc grp = do
    (bs, ConState _ cs m) <- buildConstraints $ do
      ts <- mapM (gather findExport globs env) $ snd <$> grp
      mapM_ addConstraint $ zip tvs $ snd <$> ts
      pure $ fst <$> ts
    soln <- unify cs m
    pure $ (++ acc) $ zip (fst <$> grp) $ zip (fillPlaceholders soln <$> bs) $ generalize [] . typeSolve soln <$> tvs
    where
      buildConstraints (Constraints f) = f $ ConState 0 [] M.empty
      tvs = TV . ('*':) . fst <$> grp
      env = zip (fst <$> grp) tvs ++ map (second snd) acc

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
deAnn _ = error "BUG"
