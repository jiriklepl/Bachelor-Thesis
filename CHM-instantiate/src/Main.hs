-- copied from https://github.com/visq/language-c
module Main where

import Language.C
import Language.C.System.GCC
import CHM.Transform

main = parseMyFile "test.chm" >>= typeMyAST

parseMyFile :: FilePath -> IO CTranslUnit
parseMyFile input_file =
  do parse_result <- parseCFile (newGCC "gcc") Nothing [] input_file
     case parse_result of
       Left parse_err -> error (show parse_err)
       Right ast      -> return ast

printMyAST :: CTranslUnit -> IO ()
printMyAST = print . pretty

typeMyAST :: CTranslUnit -> IO ()
typeMyAST = print . typeInfer
