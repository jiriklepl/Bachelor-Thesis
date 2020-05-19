{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
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

class Magic a where
  magic :: a -> IState [CExtDecl]


instance Magic CExtDecl where
  magic a@(CHMFDefExt _) = do
    a' <- parse a
    let (name :>: _ : _) = a'
    state@InstantiateMonad{polyTypes = pTs} <- get
    put state{polyTypes = Map.insert name (PolyType a Set.empty) pTs}
    return []
  magic a@(CHMSDefExt _) = do
    _ <- parse a
    return []
  magic a@(CDeclExt _) = return [a]
  magic a@(CFDefExt _) = do
    rtrn <- instantiate a (Forall [] ([] :=> TCon (Tycon "pointlessType" Star)))
    _ <- parse a
    return rtrn


instance Magic a => Magic [a] where
  magic as = concat <$> traverse magic as

instance Magic CTranslUnit where
  magic (CTranslUnit cExtDecls _) = magic cExtDecls

doMagic :: CTranslUnit -> CTranslUnit
doMagic (CTranslUnit cExtDecls nodeInfo) = CTranslUnit
  (evalState (magic cExtDecls) initInstantiateMonad)
  nodeInfo
