module Main where

import Autosubst.Parser
import Autosubst.Signature
import Autosubst.Types
import Autosubst.GenM
import Autosubst.GenDot
import Autosubst.GenCoq
import System.IO
import System.Directory
import System.Environment
import Options.Applicative
import Data.Semigroup ((<>))
import Text.PrettyPrint.Leijen (Doc,renderPretty,displayS)

-- cmd argument structure
data Arguments = Args
  { inputFile :: Maybe String
  , forceOverwrite :: Bool
  , coqFile :: Maybe String
  , dotFile :: Maybe String
  , lineWidth :: Int } deriving (Show)

-- the parser for comamnd line args
args :: Parser Arguments
args = Args
  <$> (optional $ strOption
      ( long "input"
      <> short 'i'
      <> metavar "SPEC"
      <> help "File containing the syntax specification. Reads from stdin if omitted." ))
  <*> switch
      ( short 'f'
      <> help "If set, program writes output files without checking if said files already exist.")
  <*> (optional $ strOption
      ( long "output"
      <> short 'o'
      <> metavar "OUT"
      <> help "The generated Coq source file. Writes to stdout if omitted." ))
  <*> (optional $ strOption
      ( long "dot"
      <> short 'd'
      <> metavar "DOT"
      <> help "Specify if diagnostic containment graph should be written out in dor format." ))
  <*> option auto
      ( long "width"
      <> short 'w'
      <> metavar "WIDTH"
      <> value 140
      <> help "Sets the line width of the output document to WIDTH. Defaults to 140 characters.")

-- top level combines busniess logic and argument parsing
main :: IO ()
main = mainProg =<< execParser opts
  where
    opts = info (args <**> helper)
      ( fullDesc
     <> progDesc "Compiles a HOAS style syntax specification SPEC to a Coq source file with corresponding inductively defined de Bruijn sorts and corresponding multivariate parallel substitution operations. Optionally outputs structural information of the specification as a dot graph highlighting the dependency structures between the various sorts."
     <> header "Autosubst 2 - Automatically generating substitutions for mutually recursive syntactic specifications" )

--
-- the actual business logic
--

-- writes a file. if the file already exists, the user is prompted for overwrite permission
-- the boolean flag is used to force write and don't prompt
writeFileOverwriteProtected :: Bool -> FilePath -> String -> IO ()
writeFileOverwriteProtected forced file content = do
  exists <- doesFileExist file
  if forced || not exists
    then writeFile file content
    else do
      putStr $ "The file " ++ file ++ " already exists; overwrite? [y/n] "
      hFlush stdout
      c <- getLine
      if c /= "y"
        then putStrLn $ "Not writing to " ++ file ++ " ..."
        else writeFile file content

generate :: Arguments -> Signature -> IO ()
generate args sig = do
  let dotGraphE = runSig sig printDot
  case (dotFile args) of
    Just df -> either putStrLn (writeFileOverwriteProtected (forceOverwrite args) df) dotGraphE
    Nothing -> return ()
  let prettyCodeE = either Left (Right . ($ "") . displayS . renderPretty 1.0 (lineWidth args)) $ runGen sig generateCoq
  case (coqFile args) of
    Just out -> either putStrLn (writeFileOverwriteProtected (forceOverwrite args) out) prettyCodeE
    Nothing -> putStrLn $ either id id prettyCodeE

mainProg :: Arguments -> IO ()
mainProg args = do
  specification <- case (inputFile args) of
    Just file -> parseFile file
    Nothing -> parseStdIn
  either putStrLn (generate args) $ either Left buildSignature specification
