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

-- | For the command line options
data CommandOptions = CommandOptions
  { output    :: String
  , outDir    :: String
  , files     :: [FilePath]
  , cCompiler :: String
  , compOpts  :: CompilerOptions
  , innerCode :: Bool
  }
  deriving (Show)

-- | The default values for the various options
initCommandOptions :: CommandOptions
initCommandOptions = CommandOptions
  { output = "a.out"
  , outDir = "."
  , files = []
  , cCompiler = "gcc"
  , compOpts = CompilerOptions
      { tDepth = 500
      }
  , innerCode = False
  }

-- | The ENTRY point of the executable
main = getArgs >>= parseArgs initCommandOptions

-- | The function that handles command line arguments
parseArgs :: CommandOptions -> [String] -> IO ()

-- | The case for options
parseArgs opts (('-':option):rest) = case option of
  -- short options
  "h" -> usage
  "v" -> version
  "o" -> output
  "d" -> directory
  "n" -> depth
  "i" -> inner
  -- long options
  "-help" -> usage
  "-version" -> version
  "-output" -> output
  "-directory" -> directory
  "-depth" -> depth
  "-inner" -> inner
  _ -> hPutStrLn stderr $
    "Error: -" ++ option ++ ": Unrecognized or malformed option"
  where -- here go the definitions of the effects of the options
    usage = printUsage stdout >> exitSuccess
    version = printVersion >> exitSuccess
    inner = parseArgs opts{innerCode=True} rest

    -- this is a template for options taking an argument
    argOpt newOpts err = if null rest
      then hPutStrLn stderr
        err
      else
        parseArgs newOpts $ tail rest
    output = argOpt
      opts{output = head rest}
      "Error: Expected an output <file> after the -o option"
    directory = argOpt
      opts{outDir = head rest}
      "Error: Expected a directory <dir> for the temporary files"
    depth = argOpt
      opts{compOpts = (compOpts opts){tDepth = read (head rest)}}
      "Error: Expected a maximum <depth> of the instance types"
-- adding a file to the list of files
parseArgs opts (file:rest) = do
  parseArgs opts{files = file : files opts} rest

{- |
  The bottom case that actually runs the compiler after
  the function goes through all the options and files.
-}
parseArgs opts []
  | null (files opts) = do
    hPutStrLn stderr "Error: No input files"
    printUsage stderr
    fileErrorExit
  | innerCode opts = do
    sequence_
      [ case takeExtension file of
          ".chm" -> do
            exists <- doesFileExist file
            unless exists $ do
              hPutStrLn stderr $
                "Error: " ++ file ++ ": No such file or directory"
              fileErrorExit
            putStrLn $ file ++ ":"
            ast <- parseFile file
            printTransformedAST ast
          ".c" -> putStrLn $ "Skipping the .c file: " ++ file
          _ -> do
            hPutStrLn stderr $
              "Error: Unknown file extension for the file: " ++ file
            fileErrorExit
      | file <- reverse $ files opts
      ]
  | otherwise = do
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
              "Error: Unknown file extension for the file: " ++ file
            fileErrorExit
      | file <- reverse $ files opts
      ]
    (_, _, _, pHandle) <- createProcess $
      proc
        (cCompiler opts)
        ("-o" : output opts : "stl.c" : paths)
    waitForProcess pHandle >>= exitWith

printUsage handle = hPutStr handle "Usage: [options] file...\n\
\  -d, --directory <dir>   Put the temporary files to <dir>, defaults to '.'\n\
\  -h, --help              Print this information\n\
\  -i, --inner             Prints the inner representation of the code considered by the type inference algorithm\n\
\  -n, --depth <depth>     Set the maximum allowed <depth> of instance types, defaults to 500\n\
\  -o, --output <file>     Write the output to <file>, defaults to 'a.out'\n\
\  -v, --version           Print the version information\n\
\"

printVersion = putStrLn "The CHM compiler (v 0.1.0.0)"

-- | Parses the filem outputing the AST
parseFile :: FilePath -> IO CTranslUnit
parseFile input_file =
  do parse_result <- parseCFile (newGCC "gcc") Nothing [] input_file
     case parse_result of
       Left parse_err -> error (show parse_err)
       Right ast      -> return ast

-- | Transforms the AST to the inner form and then prints it
printTransformedAST :: CTranslUnit -> IO ()
printTransformedAST = print . getTransformResult

printAST :: CTranslUnit -> IO ()
printAST = print
