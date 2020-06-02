-- copied from https://github.com/visq/language-c
module Main where

import Language.C
import Language.C.System.GCC
import CHM.Transform
import CHM.Instantiate

main = do
  ast <- parseMyFile "test.chm"
  -- transformAST ast
  -- typeAST ast
  itsAKindOfMagic ast

parseMyFile :: FilePath -> IO CTranslUnit
parseMyFile input_file =
  do parse_result <- parseCFile (newGCC "gcc") Nothing [] input_file
     case parse_result of
       Left parse_err -> error (show parse_err)
       Right ast      -> return ast

itsAKindOfMagic :: CTranslUnit -> IO ()
itsAKindOfMagic = doMagic

printPretty :: CTranslUnit -> IO ()
printPretty = print . pretty

printAST :: CTranslUnit -> IO ()
printAST = print

typeAST :: CTranslUnit -> IO ()
typeAST = print . runInfer

transformAST :: CTranslUnit -> IO ()
transformAST = print . getTransformResult
