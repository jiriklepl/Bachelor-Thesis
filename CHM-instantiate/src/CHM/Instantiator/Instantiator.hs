module CHM.Instantiator where
import Data.List (isSuffixOf)
import qualified Data.Set as Set
import Text.PrettyPrint.HughesPJ
import Debug.Trace {- for warnings -}
import Prelude hiding ((<>))

import Language.C.Data
import Language.C.Syntax

import CHM.InstantiatorMonad



class Instantiate p where
  instantiate :: p -> [(Ident, Ident)] -> InstantiatorMonad p
