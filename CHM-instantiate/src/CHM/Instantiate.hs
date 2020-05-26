{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module CHM.Instantiate where

import Debug.Trace

import Control.Monad.State
import Control.Monad((>=>), when)
import qualified Data.Set as Set
import qualified Data.Map as Map

import TypingHaskellInHaskell hiding (modify)

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
    let (name :>: scheme : _) = a'
    createPolyType name scheme a
    return []
  magic a@(CHMSDefExt (CHMStructDef (CHMHead chmIdents _ _) cStructUnion _)) = do
    _ <- parse a
    let
      name = getCName a
      sKind = takeNKind $ length chmIdents
      sType = TCon $ Tycon name sKind
    createPolyStruct name (toScheme sType) a
    return []
  magic a@(CDeclExt _) = do
    _ <- parse a
    return [a]
  magic a@(CFDefExt _) = do
    instantiate a (Forall [] ([] :=> TCon (Tycon "pointlessType" Star)))
    parse a
    gets (reverse . cProgram)
  magic a@(CHMCDefExt (CHMCDef (Ident cName _ _) chmHead cExtDecls _)) = do
    a' <- parse a
    let
      assumpMap = Map.fromList $ (\(fName :>: fScheme) -> (fName, fScheme)) <$> a'
    sequence_
      [ let
          fName = getCName cExtDecl
          fScheme = assumpMap Map.! fName
        in createClassPolyType cName fName fScheme cExtDecl
      | cExtDecl <- cExtDecls
      ]
    return []

  -- TODO: CHMIDefHead
  magic a@(CHMIDefExt (CHMIDef iName (CHMParams chmTypes _) cExtDecls _)) = do
    a' <- parse a
    parType <- runTState $ createParamsType <$> traverse transformCHMType chmTypes
    sequence_
      [ let
          fName = getCName cExtDecl
        in addPTypeInstance fName parType cExtDecl
      | cExtDecl <- cExtDecls
      ]
    return []

instance Magic a => Magic [a] where
  magic as = concat <$> traverse magic as

instance Magic CTranslUnit where
  magic (CTranslUnit cExtDecls _) = magic cExtDecls

doMagic :: CTranslUnit -> CTranslUnit
doMagic (CTranslUnit cExtDecls nodeInfo) = CTranslUnit
  (evalState (magic cExtDecls) initInstantiateMonad)
  nodeInfo
