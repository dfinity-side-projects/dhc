{-# LANGUAGE CPP #-}
module Parse (parseDfnHs, lexOffside, TopLevel(..), QQuoter) where
#ifndef __HASTE__
import qualified Data.ByteString.Char8 as B
import Data.ByteString.Short (ShortByteString, toShort)
#endif
import Control.Arrow
import Control.Monad
import Data.Bool
import Data.List
import qualified Data.Map.Strict as M
import Data.Map.Strict (Map)
import Data.Maybe
import Text.Parsec
import Text.Parsec.Pos

import Ast

sbs :: String -> ShortByteString
#ifdef __HASTE__
sbs = id
type ShortByteString = String
#else
sbs = toShort . B.pack
#endif

type QQuoter = String -> String -> Either String String
data LexemeType = LexString | LexNumber | LexReserved | LexVar | LexCon | LexSpecial | LexVarSym | LexQual | IndError | IndCurly | IndAngle deriving (Eq, Show)
type Lexeme = (SourcePos, (LexemeType, String))
type Lexer = Parsec String QQuoter

reservedIds :: [String]
reservedIds = words "class data default deriving do else foreign if import in infix infixl infixr instance let module newtype of then type where _"

reservedOps :: [String]
reservedOps = ["..", "::", "=", "|", "<-", "->", "=>"]

rawTok :: Lexer Lexeme
rawTok = do
  pos <- getPosition
  r <- oxford <|> symbol <|> qId <|> num <|> special <|> str
  filler
  pure (pos, r)
  where
  lowId = do
    s <- (:) <$> (lower <|> char '_') <*> many (alphaNum <|> oneOf "_'")
    pure (if s `elem` reservedIds then LexReserved else LexVar, s)
  uppId = do
    s <- (:) <$> upper <*> many (alphaNum <|> oneOf "_'")
    pure (LexCon, s)
  qId = do
    r@(_, m) <- lowId <|> uppId
    try (do
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
  oxford = do
    q <- try $ between (char '[') (char '|') $ many alphaNum
    s <- oxfordClose <|> more
    qq <- getState
    case qq q s of
      Left err -> fail err
      Right out -> pure (LexString, out)
    where
    oxfordClose = try (string "|]") >> pure ""
    more = do
      s <- innerOxford <|> (pure <$> anyChar)
      (s ++) <$> (oxfordClose <|> more)
    innerOxford = do
      q <- try $ between (char '[') (char '|') $ many alphaNum
      s <- oxfordClose <|> more
      pure $ '[':q ++ ('|':s) ++ "|]"

filler :: Lexer ()
filler = void $ many $ void (char ' ') <|> nl <|> com
  where
  nl = (char '\r' >> optional (char '\n')) <|> void (oneOf "\n\f")
  com = void $ between (try $ string "--") nl $ many $ noneOf "\r\n\f"

-- We use the `sourceColumn` of Parsec's SourcePos to record indentation.
insertIndents :: [Lexeme] -> [Lexeme]
insertIndents [] = []
-- "If the first lexeme of a module is not { or module, then it is preceded by
-- {n} where n is the indentation of the lexeme."
insertIndents (x@(p, (LexSpecial, "{")):xs) = x:ii' (Just $ sourceLine p) xs
insertIndents xs@(h:_) = (fst h, (IndCurly, "")):ii' Nothing xs

ii' :: Maybe Line -> [Lexeme] -> [Lexeme]
ii' prevLine ls = case ls of
-- "If a let, where, do, or of keyword is not followed by the lexeme {, the
-- token {n} is inserted after the keyword, where n is the indentation of the
-- next lexeme if there is one, or 0 if the end of file has been reached."
  [] -> []
  [x]
    | lwdo x -> mayAngle x ++ [(newPos "" 0 0, (IndCurly, ""))]
    | otherwise -> mayAngle x
  (x@(p, _):y:rest)
    | lwdo x && not (isLBrace y) -> mayAngle x ++ (fst y, (IndCurly, "")):ii' Nothing (y:rest)
    | otherwise -> mayAngle x ++ ii' (Just $ sourceLine p) (y:rest)
-- "Where the start of a lexeme is preceded only by white space on the same
-- line, this lexeme is preceded by < n > where n is the indentation of the
-- lexeme, provided that it is not, as a consequence of the first two rules,
-- preceded by {n}."
  where
  mayAngle x@(p, _)
    | Just l <- prevLine, l /= sourceLine p = [(p, (IndAngle, "")), x]
    | otherwise = [x]
  lwdo (_, (LexReserved, s)) | s `elem` ["let", "where", "do", "of"] = True
  lwdo _ = False
  isLBrace (_, (LexSpecial, "{")) = True
  isLBrace _ = False

-- Handle layout. See the L function in:
--   https://www.haskell.org/onlinereport/haskell2010/haskellch10.html
algL :: [Lexeme] -> [Int] -> [Lexeme]
algL a@((p, (IndAngle, _)):ts) (m:ms)
  | m == n = insL p ";" $ algL ts (m:ms)
  | m >  n = insL p "}" $ algL a ms
  where n = sourceColumn p
algL ((_, (IndAngle, _)):ts) ms = algL ts ms
algL ((p, (IndCurly, _)):ts) (m:ms) | n > m = insL p "{" $ algL ts (n:m:ms)
  where n = sourceColumn p
algL ((p, (IndCurly, _)):ts) [] | n > 0 = insL p "{" $ algL ts [n]
  where n = sourceColumn p
algL ((p, (IndCurly, _)):ts) ms = insL p "{" $ insL p "}" $ algL ((p, (IndAngle, "")):ts) ms
algL ((p, (LexSpecial, "}")):ts) (0:ms) = insL p "}" $ algL ts ms
algL ((p, (LexSpecial, "}")):_) _ = [(p, (IndError, "unmatched }"))]
-- We zero the source column of explicit open braces.
-- TODO: It should be the other way around: implicit open braces should have
-- their source column zeroed, while explicit ones should have their true
-- column value. The check in `embrace` would have to be altered to match.
algL ((p, (LexSpecial, "{")):ts) ms = insL (setSourceColumn p 0) "{" $ algL ts (0:ms)
-- See Note 5. We handle this case at a higher level, in `embrace`.
-- algL (t:ts) (m:ms) | m /= 0 && bad = insL p "}" $ algL (t:ts) ms
algL (t:ts) ms = t : algL ts ms
algL [] [] = []
algL [] (m:ms) | m /= 0 = insL (newPos "" 0 0) "}" $ algL [] ms
               | otherwise = [(newPos "" 0 0, (IndError, "unmatched {"))]

insL :: SourcePos -> String -> [Lexeme] -> [Lexeme]
insL p s = ((p, (LexSpecial, s)):)

type Parser = Parsec [Lexeme] ()
data TopLevel = Super (String, Ast)
  | ClassDecl [(String, (Type, [(String, String)]))]
  | GenDecl (String, Type)
  | DataDecl [(String, (Maybe (Int, Int), Type))]
  | PublicDecl [String]
  | StoreDecl [String]
  deriving Show

arityFromType :: Type -> Int
arityFromType = f 0 where
  f acc (_ :-> r) = f (acc + 1) r
  f acc _ = acc

header :: Parser ([TopLevel], [Lexeme])
header = do
  ps <- option [] $ want "public" >>
    between (want "(") (want ")") (var `sepBy` want ",")
  ss <- option [] $ want "store" >>
    between (want "(") (want ")") (var `sepBy` want ",")
  (,) [PublicDecl ps, StoreDecl ss] <$> getInput

data Stmt = Stmt Ast | StmtArr String Ast | StmtLet [(String, Ast)]

toplevels :: Parser [TopLevel]
toplevels = topDecls where
  embrace p = do
    m <- sourceColumn <$> getPosition
    want "{"
    let
      next = ((:) <$> p <*> sepNext) <|> sepNext
      sepNext = (want ";" >> next) <|> (want "}" >> pure []) <|> autoClose
      noMatch = obtain IndError >>= fail
      autoClose = noMatch <|> do  -- Auto-insert "}".
        when (m == 0) $ fail "cannot implicitly close an explicit open brace"
        pure []
    next
  topDecls = embrace topDecl
  topDecl = (want "data" >> simpleType)
    <|> (want "class" >> classDecl)
    -- TODO: Left-factor genDecl and sc.
    <|> genDecl <|> sc
  classDecl = do
    s <- con
    t <- tyVar
    want "where"
    ms <- embrace cDecl
    pure $ ClassDecl $ second (flip (,) [(s, t)]) <$> ms
  cDecl = do
    v <- var
    want "::"
    t <- typeExpr
    pure (v, t)
  genDecl = try $ do
    v <- var
    want "::"
    t <- typeExpr
    pure $ GenDecl (v, t)
  simpleType = do
    s <- con
    args <- many tyVar
    want "="
    let
      t = foldl' TApp (TC s) $ GV <$> args
      typeCon = do
        c <- con
        ts <- many atype
        pure (c, foldr (:->) t ts)
    typeCons <- typeCon `sepBy1` want "|"
    pure $ DataDecl [(c, (Just (i, arityFromType typ), typ))
      | (i, (c, typ)) <- zip [0..] typeCons]
  typeExpr = foldr1 (:->) <$> btype `sepBy1` want "->"
  btype = foldl1' TApp <$> many1 atype
  -- Unsupported: [] (->) (,{,}) constructors.
  atype = (TC <$> con)
    <|> (GV <$> tyVar)
    <|> (TApp (TC "[]") <$> between (want "[") (want "]") typeExpr)
    <|> (parenType <$> between (want "(") (want ")") (typeExpr `sepBy` want ","))
  parenType [x] = x
  parenType xs  = foldr1 TApp $ TC "()":xs
  sc = Super <$> letDefn
  funlhs = do
    v0 <- var
    scOp v0 <|> ((v0:) <$> many var)
  scOp l = do
    op <- varSym
    r <- var
    pure [op, l, r]
  expr = caseExpr <|> letExpr <|> doExpr <|> bin 0 False
  bin 10 _ = molecule
  bin prec isR = rec False =<< bin (prec + 1) False where
    rec isL m = try (do
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
    (fun:args) <- funlhs
    want "="
    ast <- expr
    pure (fun, if null args then ast else Ast $ Lam args ast)
  doExpr = do
    want "do"
    ss <- embrace stmt
    case ss of
      [] -> fail "empty do block"
      _ -> desugarDo ss
  desugarDo [Stmt x] = pure x
  desugarDo [] = fail "do block must end with expression"
  desugarDo (h:rest) = do
    body <- desugarDo rest
    pure $ Ast $ case h of
      Stmt x -> Ast (Ast (Var ">>=") :@ x) :@ Ast (Lam ["_"] body)
      StmtArr v x -> Ast (Ast (Var ">>=") :@ x) :@ Ast (Lam [v] body)
      StmtLet ds -> Let ds body
  stmt = stmtLet <|> do
    v <- expr
    lArrStmt v <|> pure (Stmt v)
  lArrStmt v = want "<-" >> case v of
    Ast (Var s) -> do
      x <- expr
      pure $ StmtArr s x
    _ -> fail "want variable on left of (<-)"
  stmtLet = do
    want "let"
    ds <- embrace letDefn
    (want "in" >> Stmt . Ast . Let ds <$> expr) <|> pure (StmtLet ds)
  letExpr = do
    ds <- between (want "let") (want "in") $ embrace letDefn
    Ast . Let ds <$> expr
  caseExpr = do
    x <- between (want "case") (want "of") expr
    as <- embrace alt
    when (null as) $ fail "empty case"
    pure $ Ast $ Cas x as
  alt = do
    p <- expr
    want "->"
    x <- expr
    pure (p, x)
  -- TODO: Introduce patterns to deal with _.
  lambda = fmap Ast $ Lam <$> between (want "\\") (want "->") (many1 $ var <|> uscore) <*> expr
  molecule = lambda <|> foldl1' ((Ast .) . (:@)) <$> many1 atom
  uscore = want "_" >> pure "_"
  atom = qvar
    <|> (Ast . Var <$> uscore)
    <|> (Ast . Var <$> var)
    <|> (Ast . Var <$> con)
    <|> num <|> str <|> lis <|> enumLis <|> tup
  tup = do
    xs <- between (want "(") (want ")") $ expr `sepBy` want ","
    pure $ case xs of  -- Abuse Pack to represent tuples.
      [] -> Ast $ Pack 0 0
      [x] -> x
      _ -> foldl' ((Ast .) . (:@)) (Ast $ Pack 0 $ length xs) xs

  -- TODO: Left-factor lis and enumLis.
  lis = try $ do
    items <- between (want "[") (want "]") $ expr `sepBy` want ","
    pure $ foldr (\a b -> Ast (Ast (Ast (Var ":") :@ a) :@ b)) (Ast $ Var "[]") items
  enumLis = try $ between (want "[") (want "]") $ do
    a <- expr
    want ".."
    b <- expr
    pure $ Ast $ Ast (Ast (Var "enumFromTo") :@ a) :@ b

  splitDot s = second tail $ splitAt (fromJust $ elemIndex '.' s) s
  qvar = Ast . uncurry Qual . splitDot <$> obtain LexQual
  con = obtain LexCon
  num = Ast . I . read <$> obtain LexNumber
  str = Ast . S . sbs <$> obtain LexString
  tyVar = varId

var :: Parser String
var = varId <|> try (between (want "(") (want ")") varSym)

varId :: Parser String
varId = obtain LexVar

varSym :: Parser String
varSym = obtain LexVarSym

obtain :: LexemeType -> Parser String
obtain t = token show fst f where
  f (_, (t', s)) = bool Nothing (Just s) $ t == t'

want :: String -> Parser ()
want s = void $ token show fst f where
  f (_, (LexString, _)) = Nothing
  f (_, (_, t)) | s == t = Just ()
  f _ = Nothing

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

parseDfnHs :: QQuoter -> String -> Either ParseError [TopLevel]
parseDfnHs qq s = do
  lexStream <- runParser (filler >> many rawTok) qq "" s
  (r0, rest) <- parse header "" lexStream
  fmap (r0 ++) $ parse toplevels "" $ (`algL` []) $ insertIndents rest

lexOffside :: String -> Either ParseError [String]
lexOffside s = map (snd . snd) . (`algL` []) . insertIndents
  <$> runParser (filler >> many rawTok) (\_ _ -> Left "no qq") "" s
