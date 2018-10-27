module Autosubst.Parser
  ( parseFrom -- for testing
  , parseFile
  , parseStdIn
  ) where

import Text.Parsec hiding (token, tokens, satisfy)
import Text.Parsec.String
import Control.Applicative ((<*),(*>),(<$>),(<*>))
import Control.Monad.Except
import Control.Monad.State
import qualified Data.Map as M
import qualified Data.Set as S
import Data.Either (partitionEithers)
import Autosubst.Types

--
-- ** Lexing ** from String to [TokenPos]
--

data Token = Ident String | Comment String | LParen | RParen | KColon | KType | KArrow deriving (Show, Eq)

type TokenPos = (Token, SourcePos)

parsePos :: Parser Token -> Parser TokenPos
parsePos p = flip (,) <$> getPosition <*> p

ident :: Parser Token
ident = Ident <$> ((:) <$> oneOf firstChar <*> (many $ oneOf rest))
  where firstChar = ['A'..'Z'] ++ ['a'..'z']
        rest      = firstChar ++ ['0'..'9']

comm :: Parser Token
comm = Comment <$> (string "--" *> (many $ noneOf "\n"))

identifier, comment, lparen, rparen, ktype, karrow, kcolon :: Parser TokenPos
identifier = parsePos $ ident
comment = parsePos $ comm
lparen = parsePos $ char '(' >> return LParen
rparen = parsePos $ char ')' >> return RParen
kcolon = parsePos $ char ':' >> return KColon
ktype = parsePos $ string "Type" >> return KType
karrow = parsePos $ string "->" >> return KArrow

token :: Parser TokenPos
token = choice [lparen, rparen, kcolon, try ktype, identifier, try comment, karrow]

tokens :: Parser [TokenPos]
tokens = spaces *> many (token <* spaces)

tokenize :: SourceName -> String -> Either ParseError [TokenPos]
tokenize = runParser tokens ()

--
-- ** Parsing ** from [TokenPos] to SpecAST
--

type SpecAST = ([TId], [ConstructorAST])
type ConstructorAST = (CId, TypeAST)
data TypeAST = AtomAST TId | ArrowAST TypeAST TypeAST deriving Show

-- a Parser on streams of Tokens, tagged with source positions
type TokParser a = Parsec [TokenPos] () a

advance :: SourcePos -> t -> [TokenPos] -> SourcePos
advance _ _ ((_, pos) : _) = pos
advance pos _ [] = pos

satisfy :: (TokenPos -> Bool) -> TokParser Token
satisfy f = tokenPrim show advance (\c -> if f c then Just (fst c) else Nothing)

-- Utility parser that recognizes (and yields) a specific token in the input stream
tok :: Token -> TokParser Token
tok t = (satisfy $ (== t) . fst) <?> show t

-- Test to recognize a generic comment in the input stream,
-- used for filtering out comments later.
isComment :: TokenPos -> Bool
isComment (Comment _, _) = True
isComment _ = False

-- Test to recognize an identifier in the input stream,
-- used to implemnt the ID parser below.
isIdent :: TokenPos -> Bool
isIdent (Ident _ , _) = True
isIdent _ = False

-- The actual parsers

-- identifiers
parseId :: TokParser Id
parseId = do
  Ident i <- (satisfy $ isIdent)
  return i

-- constructor types
parseCType :: TokParser TypeAST
parseCType = foldr1 ArrowAST <$> parseAtomicCType `sepBy1` tok KArrow

parseAtomicCType :: TokParser TypeAST
parseAtomicCType = (tok LParen *> parseCType <* tok RParen) <|> (AtomAST <$> parseId)

-- definitions
parseDef :: TokParser (Either TId (CId, TypeAST))
parseDef = (Left <$> try parseTypeDef) <|> (Right <$> parseConstructorDef)

parseTypeDef :: TokParser TId
parseTypeDef = parseId <* tok KColon <* tok KType

parseConstructorDef :: TokParser (CId, TypeAST)
parseConstructorDef = (,) <$> parseId <*> (tok KColon *> parseCType)

-- top level ASTs
parseSpec :: TokParser SpecAST
parseSpec = partitionEithers <$> many parseDef

--
-- ** Semantic Analysis / Input Validation ** from SpecAST to Spec
--

-- State Monad for Semantic Analysis

data SaState = SaState
  { spec    :: Spec
  , usedIds :: S.Set Id
  }

type SA = StateT SaState (Except String)

runSA :: Spec -> SA () -> Either String Spec
runSA s sa = runExcept $ spec <$> execStateT sa initialState
  where initialState = SaState s S.empty

-- Incomplete (?) list of identifiers which cannot be used in Coq definitions.
reservedIds :: S.Set Id
reservedIds = S.fromList
  -- Keywords according to the Coq manual
  ["as", "at", "cofix", "else", "end", "exists", "exists2", "fix",
   "for", "forall", "fun", "if", "IF", "in", "let", "match", "mod",
   "Prop", "return", "Set", "then", "Type", "using", "where", "with",
  -- Additional reserved identifiers
   "lazymatch", "multimatch", "Definition", "Fixpoint", "CoFixpoint",
   "Axiom", "Inductive", "CoInductive", "Theorem"]

declareId :: Id -> SA ()
declareId x = do
  ids <- usedIds <$> get
  if x `S.member` ids
    then throwError $ "identifier '" ++ x ++ "' is defined twice"
    else if x `S.member` reservedIds
    then throwError $ "identifier '" ++ x ++ "' is reserved"
    else modify $ \state -> state{ usedIds = S.insert x ids }

declareConstructor :: TId -> Constructor -> SA ()
declareConstructor tp c =
  modify $ \state -> state{ spec = updateSpec $ spec state }
  where updateSpec = M.insertWith (flip (++)) tp [c]

checkTId :: TId -> SA ()
checkTId tp = do
  s <- spec <$> get
  if tp `M.member` s
    then return ()
    else throwError $ "unknown type '" ++ tp ++ "'"

-- Check specifications

checkPosition :: TypeAST -> SA Position
checkPosition (AtomAST x) = do
  checkTId x
  return $ Position [] x
checkPosition (ArrowAST (AtomAST x) b) = do
  checkTId x
  Position bs a <- checkPosition b
  return $ Position (x:bs) a
checkPosition _ = throwError "third-order constructors are not supported"

checkPositions :: TypeAST -> SA ([Position], TId)
checkPositions (AtomAST x) = return ([], x)
checkPositions (ArrowAST b tp) = do
  p <- checkPosition b
  (ps, t) <- checkPositions tp
  return (p:ps, t)

checkConstructor :: ConstructorAST -> SA ()
checkConstructor (x,typ) = do
  declareId x
  (ps,tp) <- checkPositions typ
  declareConstructor tp (Constructor x ps)

checkSpec :: SpecAST -> Either String ([TId],Spec)
checkSpec (tps, cs) = do
  spec <- runSA emptySpec $ declareTypes >>  mapM_ checkConstructor cs 
  return (tps, spec)
  where emptySpec = M.fromList $ map (\k -> (k,[])) tps
        declareTypes = mapM_ declareId tps

--
-- ** Top Level Interface **
--

parseFrom :: String -> String -> Either String ([TId],Spec)
parseFrom src input =
  case tokenize src input of
    Left err -> Left $ show err
    Right ts -> either (Left . show) checkSpec $ runParser parseSpec () src . filter (not . isComment) $ ts

parseFile :: FilePath -> IO (Either String ([TId],Spec))
parseFile f = do
  input <- readFile f
  return $ parseFrom f input

parseStdIn :: IO (Either String ([TId],Spec))
parseStdIn = do
  s <- getContents
  return $ parseFrom ":stdin:" s

--
-- ** Testing Interface **
--

testParser :: String -> String -> IO ()
testParser src cnt =
  case tokenize src cnt of
    Left e    -> putStrLn $ show e
    Right ts' -> parseTest parseSpec . filter (not . isComment) $ ts'
