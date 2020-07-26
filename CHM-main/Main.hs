module Main where

import Control.Monad
import Data.Foldable

import System.Directory
import System.Environment
import System.Exit
import System.FilePath
import System.IO
import System.Process

import Language.C
import Language.C.System.GCC
import CHM.Instantiate

fileErrorExit = exitWith (ExitFailure 1)

data CommandOptions = CommandOptions
  { output    :: String
  , outDir    :: String
  , files     :: [FilePath]
  , cCompiler :: String
  , compOpts  :: CompilerOptions
  }
  deriving (Show)

initCommandOptions :: CommandOptions
initCommandOptions = CommandOptions
  { output = "a.out"
  , outDir = "."
  , files = []
  , cCompiler = "gcc"
  , compOpts = CompilerOptions
      { tDepth = 500
      }
  }

parseArgs :: CommandOptions -> [String] -> IO ()

parseArgs opts (('-':option):rest) = case option of
  "h" -> usage
  "v" -> version
  "o" -> output
  "d" -> directory
  "n" -> depth
  "-help" -> usage
  "-version" -> version
  "-output" -> output
  "-directory" -> directory
  "-depth" -> depth
  _ -> hPutStrLn stderr $
    "Error: -" ++ option ++ ": Unrecognized or malformed option"
  where
    usage = printUsage stdout >> exitSuccess
    version = printVersion >> exitSuccess
    argOpt newOpts err = if null rest
      then hPutStrLn stderr
        err
      else
        parseArgs newOpts $ tail rest
    output = argOpt
      opts{output = head rest}
      "Error: expected an output file after the -o option"
    directory = argOpt
      opts{outDir = head rest}
      "Error: expected a directory for the temporary files"
    depth = argOpt
      opts{compOpts = (compOpts opts){tDepth = read (head rest)}}
      "Error: expected an output file after the -o option"
parseArgs opts (file:rest) = do
  parseArgs opts{files = file : files opts} rest

parseArgs opts [] = if null (files opts)
  then do
    hPutStrLn stderr "Error: No input files"
    printUsage stderr
    fileErrorExit
  else do
    paths <- sequence
      [ case takeExtension file of
          ".chm" -> do
            exists <- doesFileExist file
            unless exists $ do
              hPutStrLn stderr $
                "Error: " ++ file ++ ": No such file or directory"
              fileErrorExit
            (path, handle) <- openTempFile
              (outDir opts)
              (replaceExtension file "c")
            ast <- parseFile file
            traverse_ (hPrint handle . pretty) $
              execMagicWith (compOpts opts) ast
            hClose handle
            return path
          ".c" -> return file
          _ -> do
            hPutStrLn stderr $
              "unknown file extension for the file: " ++ file
            fileErrorExit
      | file <- reverse $ files opts
      ]
    (_, _, _, pHandle) <- createProcess $
      proc
        (cCompiler opts)
        ("-o" : output opts : "stl.c" : paths)
    waitForProcess pHandle >>= exitWith


main = getArgs >>= parseArgs initCommandOptions

printUsage handle = hPutStr handle "Usage: [options] file...\n\
\  -d, --directory <dir>   put the temporary files to <dir>, defaults to '.'\n\
\  -h, --help              print this information\n\
\  -n, --depth <depth>     set the maximum allowed <depth> of instance types, defaults to 500\n\
\  -o, --output <file>     write the output to <file>, defaults to 'a.out'\n\
\  -v, --version           print the version information\n\
\"
printVersion = putStrLn "The CHM compiler (v 0.1.0.0)" -- TODO

parseFile :: FilePath -> IO CTranslUnit
parseFile input_file =
  do parse_result <- parseCFile (newGCC "gcc") Nothing [] input_file
     case parse_result of
       Left parse_err -> error (show parse_err)
       Right ast      -> return ast

printPretty :: CTranslUnit -> IO ()
printPretty = print . pretty

printAST :: CTranslUnit -> IO ()
printAST = print
