module CHM.Instantiator where

import Data.Map.Strict as Map
import Debug.Trace {- for warnings -}
import Prelude hiding ((<>))

import Language.C.Data
import Language.C.Syntax

import CHM.InstantiatorMonad

class Instantiate p where
  -- instantiates functions and structs/unions/enumerations by
  -- being called recursively on their children
  instantiate :: (Map Ident Ident) -> p -> p
