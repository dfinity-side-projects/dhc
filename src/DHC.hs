{-# LANGUAGE CPP #-}
#ifdef __HASTE__
{-# LANGUAGE PackageImports #-}
#endif
module DHC
  ( AstF(..), Ast(..), Clay(..), Type(..)
  , parseDefs
  , arityFromType, hsToAst, liftLambdas
  ) where
import Control.Arrow
import Control.Monad
#ifdef __HASTE__
import "mtl" Control.Monad.State
#else
import Control.Monad.Reader
import Control.Monad.State
#endif
import Data.Char
import Data.List
import qualified Data.Map.Strict as M
import Data.Map.Strict (Map)
import Data.Maybe
import Data.Traversable

import Ast
import Boost
import Parse

type QualType = (Type, [(String, String)])
data Clay = Clay
  -- Public and secret functions are accompanied by a list of their
  -- arguments types and a program for decoding them from the heap.
  { publics :: [(String, [(Type, Ast)])]
  , secrets :: [(String, [(Type, Ast)])]
  , stores :: [(String, Type)]
  , funTypes :: Map String QualType
  , supers :: Map String Ast
  , genDecls :: [(String, Type)]
  , datas :: Map String (Maybe (Int, Int), Type)
  -- | e.g. "==" -> (type "a -> a -> Bool", 0, ("Eq", "a"))
  -- The number is the method's index in the sorted list of methods.
  , methods :: Map String (Type, Int, (String, String))
  -- | e.g. "Monad" -> [">>=", "pure"]. List is sorted.
  , classes :: Map String [String]
  -- We delay processing instance declarations until after all class
  -- definitions have been handled, including those from the prelude.
  , preInstances :: [([(String, String)], String, Type, [(String, Ast)])]
  -- | e.g. "Monad" ->
  --   [ (TC "Maybe", Ast of tuple (maybe->>=, maybe-pure))
  --   , (TC "IO", Ast of tuple (io->>=, io-pure))
  --   ]
  , instances :: Map String [(QualType, Ast)]
  , recursiveCompile :: String -> String
  }

newClay :: (String -> String) -> [TopLevel] -> Either String Clay
newClay rCompile ts = do
  p0 <- foldM f emptyClay ts
  let missing = (fst <$> publics p0) \\ M.keys (supers p0)
  unless (null missing) $ Left $ "missing public functions: " ++ show missing
  let
    storeCons s
      | Just ty <- lookup s $ genDecls p0 = (s, ty)
      | otherwise = (s, TC "Store" `TApp` TV ('@':s))
  pure $ p0 { stores = storeCons . fst <$> stores p0 }
  where
  emptyClay = Clay [] [] [] M.empty M.empty [] M.empty M.empty M.empty [] M.empty rCompile
  f p t = case t of
    Super (name, ast) -> Right p { supers = M.insert name ast $ supers p }
    ClassDecl s ty unsorted -> Right p
      { methods = m1
      , classes = M.insert s (fst <$> xs) $ classes p
      }
      where
      xs = sortOn fst unsorted
      m1 = foldl' addMethod (methods p) $ zip [0..] xs
      addMethod m (idx, (mName, mType)) = M.insert mName (mType, idx, (s, ty)) m
    InstanceDecl ctx cl ty is -> Right p
      { preInstances = (ctx, cl, ty, sortOn fst is):preInstances p }
    GenDecl x -> Right p { genDecls = x:genDecls p }
    DataDecl xs -> Right p { datas = foldl' (\m (k, v) -> M.insert k v m) (datas p) xs }
    PublicDecl xs -> Right p { publics = zip xs $ repeat [] }
    StoreDecl xs -> Right p { stores = zip xs $ repeat undefined }

-- | Adds a dictionary object for a given instance, along with supercombinators
-- for each of the method implementations.
--
-- A dictionary is a tuple of `Var` nodes that refer to this instance's
-- implementation of the methods, ordered lexicographically.
-- Must be run after processing class declarations.
--
-- If there is only one method in the typeclass, then instead of a tuple of
-- size 1, we generate a single Var node.
--
-- For example, the Maybe Monad instance results in the tuple:
--
--   (Var "Maybe->>=", Var "Maybe-pure")
--
-- along with the supercombinators:
--
--   (Maybe->>=) x f = case x of { Nothing -> Nothing; Just a -> f a }
--   (Maybe-pure) x = Just x"
--
-- Actually, the generated prefixes are uglier because we just use `show`,
-- which produces "TC \"Maybe\"" instead of "Maybe".
mkDict :: Clay -> ([(String, String)], String, Type, [(String, Ast)]) -> Either String Clay
mkDict p (ctx, cls, ty, is) = case M.lookup cls $ classes p of
  Nothing -> Left $ "unknown typeclass: " ++ cls
  Just ms -> do
    when (sorted /= ms) $ Left $ "instance methods disagree with class: " ++ cls ++ " " ++ show ty
    Right p
      { instances = M.insertWith (++) cls [((ty, ctx), dict)] $ instances p
      , supers = supers p `M.union` M.fromList (first (methodPrefix ty) <$> is)
      }
    where
    dict | [one] <- sorted = Ast $ Var $ methodPrefix ty one
         | otherwise = foldl' ((Ast .) . (:@)) (Ast $ Pack 0 $ length is) $ Ast . Var . methodPrefix ty <$> sorted
    sorted = sort $ fst <$> is

methodPrefix :: Type -> String -> String
methodPrefix ty method = concat [show ty, "-", method]

hsToAst :: Boost -> QQuoter -> String -> Either String Clay
hsToAst boost qq prog = do
  cl0 <- showErr $ newClay (either error id . qq "wasm") =<< either (Left . show) Right (parseDfnHs qq prog)
  preludeDefs <- parseDefs $ boostPrelude boost
  let
    cl1 = extractSecrets cl0
      { supers = supers preludeDefs `M.union` supers cl0
      , datas = datas preludeDefs `M.union` datas cl0
      , methods = methods preludeDefs `M.union` methods cl0
      , classes = classes preludeDefs `M.union` classes cl0
      , preInstances = preInstances preludeDefs ++ preInstances cl0
      }
  cl <- foldM mkDict cl1 $ preInstances cl1
  (inferred, storageCons) <- inferType boost cl
  let
    -- TODO: Handle non-strict case expressions.
    subbedDefs =
        (second expandCase <$>)
      . liftLambdas
      -- Saturating constructors may create lambdas, so must occur before
      -- we lift lambdas.
      . (second saturateCons <$>)
      . (second snd <$>) $ inferred
    types = M.fromList $ second fst <$> inferred
    stripStore (TApp (TC "Store") t) = t
    stripStore _ = error "expect Store"
    addDecoders :: String -> (String, [(Type, Ast)])
    addDecoders s = (s, addDec [] ty)
      where
      Just (ty, _) = M.lookup s types
      addDec acc t = case t of
        a :-> b -> addDec ((a, dictSolve inferred cl [] M.empty $ Ast (Placeholder "dfromUnboxed" a)) : acc) b
        TApp (TC "IO") (TC "()") -> reverse acc
        _ -> error "exported functions must return IO ()"
  pure cl
    { publics = addDecoders . fst <$> publics cl
    , secrets = addDecoders . fst <$> secrets cl
    , supers = M.fromList subbedDefs
    , funTypes = types
    , stores = second (stripStore . typeSolve storageCons) <$> stores cl }
  where
  showErr = either (Left . show) Right

justHere :: QQuoter
justHere "here" s = Right s
justHere _ _ = Left "bad scheme"

parseDefs :: String -> Either String Clay
parseDefs s = newClay undefined =<< either (Left . show) Right (parseDfnHs justHere s)

-- The Constraints monad combines a State monad and an Either monad.
-- The state consists of the set of constraints and next integer available
-- for naming a free variable, and the contexts of each variable.
data ConState = ConState
  String -- Prefix for generated free variables.
  Int  -- Integer for next free variable name.
  [(Type, Type)]  -- Constraints added so far.
  (Map String [String])  -- Contexts of each variable.
newtype Constraints a = Constraints (ConState -> Either String (a, ConState))

buildConstraints :: String -> Constraints a -> Either String (a, ConState)
buildConstraints pre (Constraints f) = f $ ConState pre 0 [] M.empty

instance Functor Constraints where fmap = liftM
instance Applicative Constraints where { (<*>) = ap ; pure = return }
instance Monad Constraints where
  Constraints c1 >>= fc2 = Constraints $ \cs -> case c1 cs of
    Left err -> Left err
    Right (r, cs2) -> let Constraints c2 = fc2 r in c2 cs2
  return a = Constraints $ \p -> Right (a, p)

newTV :: Constraints Type
newTV = Constraints $ \(ConState pre i cs m) -> Right (TV $ pre ++ show i, ConState pre (i + 1) cs m)

addConstraint :: (Type, Type) -> Constraints ()
addConstraint c = Constraints $ \(ConState pre i cs m) -> Right ((), ConState pre i (c:cs) m)

addContext :: String -> String -> Constraints ()
addContext s x = Constraints $ \(ConState pre i cs m) -> Right ((), ConState pre i cs $ M.insertWith union x [s] m)

type Globals = Map String (Maybe (Int, Int), Type)

-- | Gathers constraints.
-- Replaces overloaded methods with Placeholder.
-- Replaces data constructors with Pack.
-- For DFINITY, replaces `my.f` with `#preslot n` where n is the slot number
-- preloaded with the secret or public function `f`.
gather
  :: Clay
  -> Globals
  -> [(String, QualType)]
  -> Ast
  -> Constraints (AAst Type)
gather cl globs env (Ast ast) = case ast of
  I i -> pure $ AAst (TC "Int") $ I i
  S s -> pure $ AAst (TC "String") $ S s
  Pack m n -> do  -- Only tuples are pre`Pack`ed.
    xs <- replicateM n newTV
    let r = foldr1 TApp $ TC "()":xs
    pure $ AAst (foldr (:->) r xs) $ Pack m n
  Qual "my" f
    | Just n <- elemIndex f (fst <$> publics cl ++ secrets cl) -> rec env $ Ast (Ast (Var "#preslot") :@ Ast (I $ fromIntegral n))
    | otherwise -> bad $ "must be secret or public: " ++ f
  Var "_" -> do
    x <- newTV
    pure $ AAst x $ Var "_"
  Var v
    | Just qt <- lookup v env -> do
      (t1, qs1) <- instantiate qt
      pure $ foldl' ((AAst t1 .) . (:@)) (AAst t1 $ Var v) $ (\(a, b) -> AAst (TC $ "Dict-" ++ a) $ Placeholder a (TV b)) <$> qs1
    | Just (ty, _, typeClass) <- M.lookup v $ methods cl -> do
      ~(t1, [(_, x)]) <- instantiate (ty, [typeClass])
      pure $ AAst t1 $ Placeholder v $ TV x
    | Just (ma, gt) <- M.lookup v globs ->
      flip AAst (maybe (Var v) (uncurry Pack) ma) . fst <$> instantiate (gt, [])
    | otherwise -> bad $ "undefined: " ++ v
  t :@ u -> do
    a@(AAst tt _) <- rec env t
    b@(AAst uu _) <- rec env u
    x <- newTV
    addConstraint (tt, uu :-> x)
    pure $ AAst x $ a :@ b
  Lam args u -> do
    ts <- mapM (const newTV) args
    a@(AAst tu _) <- rec (zip (filter (/= "_") args) (zip ts $ repeat []) ++ env) u
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
    rec = gather cl globs
    bad = Constraints . const . Left
    afst (AAst t _) = t

-- | Instantiate generalized variables.
-- Returns type where all generalized variables have been instantiated along
-- with the list of type constraints where each generalized variable has
-- been instantiated with the same generated names.
instantiate :: QualType -> Constraints (Type, [(String, String)])
instantiate (ty, qs) = do
  (gvmap, result) <- f [] $ subStore ty
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
    pure (m2, t' :-> u')
  f m (t `TApp` u) = do
    (m1, t') <- f m t
    (m2, u') <- f m1 u
    pure (m2, t' `TApp` u')
  f m t = pure (m, t)

-- Change "Store a" -> "(AnyDfn -> IO (), IO AnyDfn)".
subStore :: Type -> Type
subStore ty = case ty of
  t :-> u -> subStore t :-> subStore u
  TC "Store" `TApp` u -> TApp (TC "()") $
    (unboxed (subStore u) :-> io (TC "()")) `TApp` io (unboxed $ subStore u)
  t `TApp` u -> subStore t `TApp` subStore u
  _ -> ty
  where
  io = TApp $ TC "IO"
  unboxed = TApp $ TC "Unboxed"

generalize
  :: [(String, (QualType, Ast))]
  -> Clay
  -> Solution
  -> (String, AAst Type)
  -> (String, (QualType, Ast))
generalize scs cl (soln, ctx) (fun, a0@(AAst t0 _)) = (fun, (qt, a1)) where
  qt@(_, qs) = runState (generalize' ctx $ typeSolve soln t0) []
  -- TODO: Compute nub of qs?
  dsoln = zip qs $ ("#d" ++) . show <$> [(0::Int)..]
  -- TODO: May be useful to preserve type annotations?
  a1 = dictSolve scs cl dsoln soln ast
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

-- Replaces e.g. `TV x` with `GV x` and adds its constraints
-- (e.g. Eq x, Monad x) to the common pool.
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

dictSolve
  :: [(String, (QualType, Ast))]
  -> Clay
  -> [((String, String), String)]
  -> Map String Type
  -> Ast
  -> Ast
dictSolve scs cl dsoln soln = ffix $ \h (Ast ast) -> case ast of
  -- Replace method Placeholders with selector and dictionary Placeholder.
  Placeholder s t | Just (_, idx, (typeClass, _)) <- M.lookup s $ methods cl ->
    case length $ classes cl M.! typeClass of
      1 -> rec (Ast $ Placeholder typeClass $ typeSolve soln t)
      _ -> Ast (DictIndex idx) @@ rec (Ast $ Placeholder typeClass $ typeSolve soln t)
  -- Replace dictionary Placeholders.
  Placeholder d t -> case typeSolve soln t of
    TV v -> Ast $ Var $ fromMaybe (error $ "unsolvable: " ++ show (d, v)) $ lookup (d, v) dsoln
    u -> findInstance d u
  _       -> Ast $ h ast
  where
  aVar = Ast . Var
  infixl 5 @@
  x @@ y = Ast $ x :@ y
  rec = dictSolve scs cl dsoln soln
  findInstance typeClass t | Just insts <- M.lookup typeClass $ instances cl
    = case matchInstance typeClass t insts of
      Nothing -> error "BUG! missing instance"
      Just ast -> rec ast
  findInstance "Message" t = Ast . CallSlot tu $ rec . Ast . Placeholder "ctoUnboxed" <$> tu
    where tu = either (error . show) id $ listFromTupleType t
  -- The "Storage" typeclass has four methods:
  --  1. toAnyRef
  --  2. fromAnyRef
  --  3. toUnboxed
  --  4. fromUnboxed
  -- For boxed types such as databufs, 1 and 2 are the same as 3 and 4.
  -- For unboxed types, such as integers, 1 encodes to a databuf, 2 decodes
  -- from a databuf, and 3 and 4 leave the input unchanged.
  findInstance "Storage" t = case t of
    TC "Databuf" -> boxy (aVar "#reduce") (aVar "#reduce")
    TC "String" -> boxy (aVar "." @@ aVar "#reduce" @@ aVar "toD") (aVar "." @@ aVar "#reduce" @@ aVar "fromD")
    TC "Port" -> boxy (aVar "#reduce") (aVar "#reduce")
    TC "Actor" -> boxy (aVar "#reduce") (aVar "#reduce")
    TC "Module" -> boxy (aVar "#reduce") (aVar "#reduce")
    TC "Int" -> Ast (Pack 0 4) @@ aVar "Int-toAny" @@ aVar "Int-fromAny" @@ aVar "#reduce" @@ aVar "#reduce"
    TC "I32" -> Ast (Pack 0 4) @@ aVar "#reduce" @@ aVar "#reduce" @@ aVar "#reduce" @@ aVar "#reduce"
    TC "Bool" -> Ast (Pack 0 4) @@ aVar "Bool-toAny" @@ aVar "Bool-fromAny" @@ aVar "Bool-toUnboxed" @@ aVar "Bool-fromUnboxed"
    TApp (TC "[]") a -> let
      ltai = aVar "list_to_any_instance" @@ rec (Ast $ Placeholder "Storage" a)
      lfai = aVar "list_from_any_instance" @@ rec (Ast $ Placeholder "Storage" a)
      in boxy ltai lfai
    TC "()" -> boxy (aVar "unit_to_any_instance") (aVar "unit_from_any_instance")
    TApp (TC "()") (TApp a b) -> let
      -- TODO: Brittle. Relies on order constraints are found.
      -- Implement contexts for instance declarations.
      ptai = aVar "pair_to_any_instance" @@ rec (Ast $ Placeholder "Storage" b) @@ rec (Ast $ Placeholder "Storage" a)
      pfai = aVar "pair_from_any_instance" @@ rec (Ast $ Placeholder "Storage" b) @@ rec (Ast $ Placeholder "Storage" a)
      in boxy ptai pfai
    e -> error $ "BUG! no Storage for " ++ show e
    where boxy to from = Ast (Pack 0 4) @@ to @@ from @@ to @@ from
  findInstance d t = error $ "BUG! bad class: " ++ show (d, t)

  matchInstance typeClass t candidates = do
    ((sol, ctx), (qt, ast)) <- lookupType cl t candidates
    let
      Just classMethods = M.lookup typeClass $ classes cl
      mAsts = mkDictEntry <$> classMethods
      -- TODO: Respect the order of the clauses in the context of `qt`.
      mkDictEntry moo = foldl' addDict (Ast $ Var $ methodPrefix (fst qt) moo) $ M.assocs ctx
      addDict a (zzz, [xxx]) = case typeSolve sol (TV zzz) of
        TV v -> let Just dv = lookup (xxx, v) dsoln
          in Ast $ a :@ Ast (Var dv)
        tt -> Ast $ a :@ Ast (Placeholder xxx tt)
      addDict _ _ = error "TODO: more than one constraint per type variable"
    case () of
      () | M.null sol -> Just ast
         | [mAst] <- mAsts -> Just mAst
         | otherwise -> Just $ foldl' ((Ast .) . (:@)) (Ast $ Pack 0 $ length classMethods) mAsts

typeSolve :: Map String Type -> Type -> Type
typeSolve soln t = case t of
  TApp a b      -> rec a `TApp` rec b
  a :-> b       -> rec a :-> rec b
  TV x          -> fromMaybe t $ M.lookup x soln
  _             -> t
  where rec = typeSolve soln

lookupType :: Clay -> Type -> [(QualType, Ast)] -> Maybe (Solution, (QualType, Ast))
lookupType _ _ [] = Nothing
lookupType cl t ((qt, ast):rest) = case unify cl cs m of
  Left _ -> lookupType cl t rest
  Right zzz -> Just (zzz, (qt, ast))
  where
  Right (_, ConState _ _ cs m) = buildConstraints "#" $ do
    (ty, _) <- instantiate qt
    addConstraint (ty, t)
    pure ()

-- | The `propagateClasses` and `propagateClassTyCon` functions of
-- "Implementing type classes".
propagate :: Clay -> [String] -> Type -> Either String [(String, [String])]
propagate _ [] _ = Right []
propagate _ cs (TV y) = Right [(y, cs)]
propagate cl cs t = concat <$> mapM propagateTyCon cs where
  propagateTyCon s | Just insts <- M.lookup s $ instances cl = case lookupType cl t insts of
    Nothing -> Left $ unwords ["no", s, "instance:", show t]
    -- For example, given `Eq [a]`, returns `Eq a`.
    Just ((_, ctx), _) -> Right $ M.assocs ctx
  propagateTyCon "Storage" = case t of
    TApp (TC "()") (TApp a b) -> (++) <$> rec ["Storage"] a <*> rec ["Storage"] b
    TApp (TC "[]") a -> rec ["Storage"] a
    TC s | elem s messageTypes -> Right []
    _ -> Left $ "no Storage instance: " ++ show t
  propagateTyCon "Message" =
    concat <$> (mapM (rec ["Storage"]) =<< listFromTupleType t)
  propagateTyCon c = error $ "TODO: " ++ c
  rec = propagate cl

-- | Returns list of types from a tuple.
-- e.g. (String, Int) becomes [String, Int]
-- This should be trivial, but we represent tuples in a weird way!
listFromTupleType :: Type -> Either String [Type]
listFromTupleType ty = case ty of
  TC "()" -> Right []
  TApp (TC "()") rest -> weirdList rest
  _ -> Right [ty]
  where
  -- Tuples are represented oddly in our Type data structure.
  weirdList tup = case tup of
    TC _ -> Right [tup]
    TV _ -> Right [tup]
    TApp h@(TC _) rest -> (h:) <$> weirdList rest
    TApp h@(TV _) rest -> (h:) <$> weirdList rest
    _ -> Left $ "want tuple: " ++ show tup

-- e.g. [TV 'a' -> TC "Int", ...], [TV 'b', ["Eq", "Ord"], ...]
type Solution = (Map String Type, Map String [String])

unify :: Clay -> [(Type, Type)] -> Map String [String] -> Either String Solution
unify cl constraints ctx = execStateT (uni cl constraints) (M.empty, ctx)

refine :: Clay -> [(Type, Type)] -> Solution -> Either String Solution
refine cl constraints = execStateT (uni cl constraints)

uni :: Clay -> [(Type, Type)] -> StateT (Map String Type, Map String [String]) (Either String) ()
uni _ [] = do
  (tm, qm) <- get
  as <- forM (M.keys tm) $ follow . TV
  put (M.fromList $ zip (M.keys tm) as, qm)
uni _ ((GV _, _):_) = lift $ Left "BUG! generalized variable in constraint"
uni _ ((_, GV _):_) = lift $ Left "BUG! generalized variable in constraint"
uni cl ((lhs, rhs):cs) = do
  z <- (,) <$> follow lhs <*> follow rhs
  case z of
    (s, t) | s == t -> rec cs
    (TV x, TV y) -> do
      when (x /= y) $ do
        (tm, qm) <- get
        -- (Ideally should union by rank.)
        put (M.insert x (TV y) tm, case M.lookup x qm of
          Just q -> M.insert y q $ M.delete x qm
          _ -> qm)
      rec cs
    (TV x, t) -> if x `elem` freeTV t
      -- TODO: Test infinite type detection.
      then lift . Left $ "infinite: " ++ x ++ " = " ++ show t
      else do
        -- The `instantiateTyvar` function of "Implementing type classes".
        (_, qm) <- get
        -- For example, Eq [a] propagates to Eq a, which we record.
        either (lift . Left) addQuals $ propagate cl (fromMaybe [] $ M.lookup x qm) t
        modify' $ first $ M.insert x t
        rec cs
    (s, t@(TV _)) -> rec $ (t, s):cs
    (TApp s1 s2, TApp t1 t2) -> rec $ (s1, t1):(s2, t2):cs
    (s1 :-> s2, t1 :-> t2) -> rec ((s1, t1):(s2, t2):cs)
    (s, t) -> lift . Left $ "mismatch: " ++ show s ++ " /= " ++ show t
  where
  addQuals = modify' . second . M.unionWith union . M.fromList
  rec = uni cl

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
boostTypes b = M.fromList $ second ((,) Nothing . fst) <$> boostPrims b

-- | Find functions used as funrefs but not declared public.
extractSecrets :: Clay -> Clay
extractSecrets cl = cl { secrets = zip (concatMap filterSecrets $ M.elems $ supers cl) $ repeat [] }
  where
  filterSecrets = bifix foldMapDefault $ \h (Ast ast) -> case ast of
    Qual "my" f -> if elem f $ fst <$> publics cl then [] else [f]
    _ -> h ast

inferType
  :: Boost
  -> Clay
  -- Returns types of definitions and stores.
  -> Either String ([(String, (QualType, Ast))], Map String Type)
inferType boost cl = foldM inferMutual ([], M.empty) $ map (map (\k -> (k, ds M.! k))) sortedDefs where
  ds = supers cl
  -- Groups of definitions, sorted in the order we should infer their types.
  sortedDefs = reverse $ scc (callees cl ds) $ M.keys ds
  -- List notation is a special case in Haskell.
  -- This is "data [a] = [] | a : [a]" in spirit.
  listPresets = M.fromList
    [ ("[]", (Just (0, 0), TApp (TC "[]") a))
    , (":",  (Just (1, 2), a :-> TApp (TC "[]") a :-> TApp (TC "[]") a))
    ] where a = GV "a"
  globs = listPresets
    `M.union` datas cl
    `M.union` boostTypes boost
    `M.union` M.fromList (second ((,) Nothing) <$> stores cl)
  inferMutual :: ([(String, (QualType, Ast))], Map String Type) -> [(String, Ast)] -> Either String ([(String, (QualType, Ast))], Map String Type)
  inferMutual (acc, accStorage) grp = do
    (typedAsts, ConState _ _ cs m) <- buildConstraints "_" $ forM grp $ \(s, d) -> do
      t <- gather cl globs env d
      addConstraint (TV $ '*':s, annOf t)
      when (s == "main") $ addConstraint (TV $ '*':s, TApp (TC "IO") $ TC "()")
      case s `lookup` genDecls cl of
        Nothing -> pure ()
        Just gt -> do
          (ty, _) <- instantiate (gt, [])
          addConstraint (TV $ '*':s, ty)
      pure (s, t)
    initSol <- unify cl cs m
    sol@(solt, _) <- foldM (checkPubSecs cl) initSol (fst <$> grp)
    let storageCons = M.filterWithKey (\k _ -> head k == '@') solt
    -- TODO: Look for conflicting storage constraints.
    pure ((++ acc) $ generalize acc cl sol <$> typedAsts, accStorage `M.union` storageCons)
    where
    annOf (AAst a _) = a
    tvs = TV . ('*':) . fst <$> grp
    env = zip (fst <$> grp) (zip tvs $ repeat []) ++ map (second fst) acc

checkPubSecs :: Clay -> Solution -> String -> Either String Solution
checkPubSecs cl (soln, ctx) s
  | s /= "main" &&  -- Already handled.
      (s `elem` (fst <$> publics cl ++ secrets cl)) =
    -- Require `public` and `secret` functions to return IO ().
    refine cl [(retType t, TApp (TC "IO") (TC "()"))] (soln, ctx)
    -- TODO: Check no free variables are left, and
    -- propagate ["Storage"] succeeds (returns []) for each argument type.
  | otherwise = Right (soln, ctx)
  where
  Just t = M.lookup ('*':s) soln
  retType (_ :-> a) = retType a
  retType r = r

-- TODO: For finding strongly-connected components, there's no need to find
-- all dependencies. If a node has already been processed, we should avoid
-- finding all its dependencies again. We can do this by passing in a list of
-- nodes that have already been explored.
callees :: Clay -> Map String Ast -> String -> [String]
callees cl ds s = snd $ execState (go s) ([], []) where
  go :: String -> State ([String], [String]) ()
  go f = do
    (env, acc) <- get
    unless (elem f (env ++ acc) || M.member f (methods cl)) $ case M.lookup f ds of
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

freeVars :: Ast -> AAst [String]
freeVars (Ast ast) = g [] ast where
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
  g _ x = ffix (\h (Ast a) -> AAst [] $ h a) $ Ast x

caseVars :: AstF Ast -> [String]
caseVars (Var v) = [v]
caseVars (Ast x :@ Ast y) = caseVars x `union` caseVars y
caseVars _ = []

saturateCons :: Ast -> Ast
saturateCons = ffix $ \h ast -> let
  (t:spine) = spinal [] ast
  in case t of
    Pack m n | n > length spine -> Ast $ Lam vars body where
      vars = show <$> [1..n - length spine]
      aVars = Ast . Var <$> vars
      body = foldl' ((Ast .) . (:@)) (Ast $ Pack m n) $ (++ aVars) $ getRs spine
    _ -> foldl' ((Ast .) . (:@)) (Ast $ h t) $ getRs spine
  where
  spinal sp (Ast ast) = case ast of
    (l :@ _) -> spinal (ast:sp) l
    _ -> ast:sp
  getRs = map (saturateCons . (\(_ :@ r) -> r))

liftLambdas :: [(String, Ast)] -> [(String, Ast)]
liftLambdas scs = existingDefs ++ newDefs where
  (existingDefs, (_, newDefs)) = runState (mapM f $ second freeVars <$> scs) ([], [])
  f (s, AAst _ (Lam args body)) = do
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
  g :: AAst [String] -> State ([String], [(String, Ast)]) Ast
  g = bifix mapM $ \h (AAst fvs ast) -> case ast of
    Let ds t -> fmap Ast $ Let <$> mapM noLamb ds <*> g t where
      noLamb (name, AAst dfvs (Lam ss body)) = do
        n <- genName
        body1 <- g body
        modify $ second ((n, Ast $ Lam (dfvs ++ ss) body1):)
        pure (name, foldl' ((Ast .) . (:@)) (Ast $ Var n) $ Ast . Var <$> dfvs)
      noLamb (name, a) = (,) name <$> g a
    lam@(Lam _ _) -> do
      n <- genName
      g $ AAst fvs $ Let [(n, AAst fvs lam)] (AAst [n] $ Var n)
    _ -> Ast <$> h ast

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
    expandAlt onFail deeper (p, a) = case fromApList p of
      [Ast (Var _)] -> (:moreCases) . (,) p <$> g deeper a
      [Ast (S s)] -> do
        v <- genVar
        a1 <- g deeper a
        pure [(Ast $ Var v, Ast $ Cas (Ast (Ast (Ast (Var "eq_String") :@ Ast (Var v)) :@ Ast (S s))) $ (Ast $ Pack 1 0, a1):moreCases)]
      [Ast (I n)] -> do
        v <- genVar
        a1 <- g deeper a
        pure [(Ast $ Var v, Ast $ Cas (Ast (Ast (Ast (Var "eq_Int") :@ Ast (Var v)) :@ Ast (I n))) $ (Ast $ Pack 1 0, a1):maybe [] (pure . (,) (Ast $ Pack 0 0)) onFail)]
      h@(Ast (Pack _ _)):xs -> (++ moreCases) <$> doPack [h] deeper xs a
      _ -> error $ "bad case: " ++ show p

      where
      moreCases = maybe [] (pure . (,) (Ast $ Var "_")) onFail
      doPack acc dpr [] body = (:moreCases) . (,) (foldl1 ((Ast .) . (:@)) acc) <$> g dpr body
      doPack acc dpr (h:rest) body = do
        gv <- Ast . Var <$> genVar
        case h of
          Ast (Var _) -> doPack (acc ++ [h]) dpr rest body
          _ -> doPack (acc ++ [gv]) (dpr ++ [(gv, h)]) rest body
      g [] body = pure body
      g ((v, w):rest) body = fmap Ast $ Cas v <$> expandAlt onFail rest (w, body)

    genVar = do
      n <- get
      put (n + 1)
      pure $ "c*" ++ show n

    fromApList :: Ast -> [Ast]
    fromApList (Ast (a :@ b)) = fromApList a ++ [b]
    fromApList a = [a]

messageTypes :: [String]
messageTypes = ["Databuf", "String", "Actor", "Module", "Port", "I32", "Int", "Bool", "()"]
