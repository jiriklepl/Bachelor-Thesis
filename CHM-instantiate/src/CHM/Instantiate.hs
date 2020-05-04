module CHM.Instantiate where

import Control.Monad.State
import Control.Monad((>=>), when)
import qualified Data.Set as Set
import qualified Data.Map as Map

import TypingHaskellInHaskell

import Language.C.Data
import Language.C.Syntax
import Language.C.Data.Ident (Ident(..))

import CHM.Transform

import CHM.InstantiateMonad

magic :: CExtDecl -> IState [CExtDecl]
magic a@(CHMFDefExt _) = do
  a' <- parse a
  let [name :>: _] = a'
  state@InstantiateMonad{polyTypes = pTs} <- get
  put state{polyTypes = Map.insert name (PolyType a Set.empty) pTs}
  return []
magic a@(CDeclExt _) = return [a]
magic a@(CFDefExt _) = return [a]

instantiate :: CTranslUnit -> IState CTranslUnit
instantiate a@(CTranslUnit cExtDecls _) = return a
