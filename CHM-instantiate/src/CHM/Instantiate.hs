{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module CHM.Instantiate where

import Debug.Trace

import Control.Monad.State
import Control.Monad((>=>), when)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Foldable

import TypingHaskellInHaskell hiding (modify)

import Language.C (Pretty(..))
import Language.C.Data
import Language.C.Syntax
import Language.C.Data.Ident (Ident(..))

import CHM.Transform

import CHM.InstantiateMonad

class Magic a where
  magic :: a -> IState ()


instance Magic CExtDecl where
  magic a@(CHMFDefExt _) = do
    a' <- parse a
    let
      name = getCName a
      Just (_ :>: scheme) = (name :>: toScheme tError) `Set.lookupLE` a'
    createPolyType name scheme a
  magic a@(CHMSDefExt (CHMStructDef (CHMHead chmIdents _ _) cStructUnion _)) = do
    parse_ a
    let
      name = getCName a
      sKind = takeNKind $ length chmIdents
      sType = TCon $ Tycon name sKind
    createPolyStruct name (toScheme sType) a
  magic a@(CDeclExt _) = do
    parse_ a
    enqueueExtDecl a
  magic a@(CFDefExt _) = do
    instantiate a (Forall [] ([] :=> TCon (Tycon "@pointlessType" Star)))
    parse_ a
    return ()
  magic a@(CHMCDefExt (CHMCDef (Ident cName _ _) chmHead cExtDecls _)) = do
    a' <- parse a
    let
      assumpMap = foldl (\m (name :>: scheme) -> Map.insert name scheme m) Map.empty a'
    sequence_
      [ let
          fName = getCName cExtDecl
          fScheme = assumpMap Map.! fName
        in createClassPolyType cName fName fScheme cExtDecl
      | cExtDecl <- cExtDecls
      ]

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

instance Magic a => Magic [a] where
  magic = traverse_ magic

instance Magic CTranslUnit where
  magic (CTranslUnit cExtDecls _) = magic cExtDecls

doMagic :: CTranslUnit -> IO ()
doMagic (CTranslUnit cExtDecls nodeInfo) =
  let state = execState (magic cExtDecls) initInstantiateMonad
  in foldl (\u decl -> u >> print (pretty decl)) (return ()) (cProgram state)
