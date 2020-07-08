{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module CHM.Instantiate where

import Debug.Trace

import Control.Monad.State
import Control.Monad((>=>), when)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Foldable

import qualified Data.ByteString.Char8 as T

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
      Just scheme = name `Map.lookup` a'
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
    instantiate a (Forall [] ([] :=> TCon (Tycon (T.pack "@pointlessType") Star)))
    parse_ a
    return ()
  magic a@(CHMCDefExt cDef) = do
    a' <- parse a
    let
      cExtDecls = case cDef of
        CHMCDef _ _ cExtDecls' _ -> cExtDecls'
        CHMCDefParams _ _ _ cExtDecls' _ -> cExtDecls'
    sequence_
      [ let
          fName = getCName cExtDecl
          fScheme = a' Map.! fName
        in createClassPolyType (getCName cDef) fName fScheme cExtDecl
      | cExtDecl <- cExtDecls
      ]

  -- TODO: CHMIDefHead not fully functional
  magic a@(CHMIDefExt chmIDef) = do
    a' <- parse a
    tState <- gets transformState
    let
      (parTypeAction, cExtDecls) = case chmIDef of
        CHMIDef iName (CHMParams chmTypes _) cExtDecls' _ ->
          (createParamsType <$> traverse transformCHMType chmTypes, cExtDecls')
        CHMIDefHead iName chmHead (CHMParams chmTypes _) cExtDecls' _ ->
          ( do
              enterCHMHead
              _ <- transform chmHead
              createParamsType <$> traverse transformCHMType chmTypes
          , (\(CFDefExt cFunDef) -> CHMFDefExt (CHMFunDef chmHead cFunDef (nodeInfo cFunDef))) <$> cExtDecls')  -- TODO: add case for two chmHeads
      (parType, _) = runState parTypeAction tState
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
