{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module CHM.InstantiateMonad where

import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List as List
import Data.Char
import Data.Maybe

import Debug.Trace

import Language.C.Syntax
import Language.C.Data
import Language.C.Data.Ident (Ident(..))

import TypingHaskellInHaskell hiding (modify)
import CHM.Transform

type IState = State InstantiateMonad

data PolyType = PolyType
  { pTypeDefinition :: CExtDecl
  , pTypeDefinitions :: Map.Map Type CExtDecl
  , pTypeClass :: Maybe Id
  , pTypeScheme :: Scheme
  , pTypeInstances  :: Set.Set Id
  }
  deriving (Show)


initPolyType :: Scheme -> CExtDecl -> PolyType
initPolyType scheme def = PolyType
  { pTypeDefinition = def
  , pTypeDefinitions = Map.empty
  , pTypeClass = Nothing
  , pTypeScheme = scheme
  , pTypeInstances = Set.empty
  }

initClassPolyType :: Id -> Scheme -> CExtDecl -> PolyType
initClassPolyType cName fScheme fDef =
  (initPolyType fScheme fDef){pTypeClass = Just cName}

data InstantiateMonad = InstantiateMonad
  { parsedAssumps  :: [Assump]
  , transformState :: TransformMonad
  , lastScopeCopy  :: Int
  , polyTypes      :: Map.Map Id PolyType
  , polyStructs    :: Map.Map Id PolyType
  , polyUnions     :: Map.Map Id PolyType
  , polyEnums      :: Map.Map Id PolyType
  , polyAnonNumber :: Int
  }

initInstantiateMonad :: InstantiateMonad
initInstantiateMonad = InstantiateMonad
  { parsedAssumps  = []
  , transformState = initTransformMonad
  , lastScopeCopy  = 0
  , polyTypes      = Map.empty
  , polyStructs    = Map.empty
  , polyUnions     = Map.empty
  , polyEnums      = Map.empty
  , polyAnonNumber = 0
  }

createPolyType :: Id -> Scheme -> CExtDecl -> IState ()
createPolyType fName fScheme fDef = do
    state@InstantiateMonad{polyTypes = pTs} <- get
    put state {polyTypes = Map.insert fName (initPolyType fScheme fDef) pTs}

createPolyStruct :: Id -> Scheme -> CExtDecl -> IState ()
createPolyStruct fName fScheme fDef = do
    state@InstantiateMonad{polyStructs = pSs} <- get
    put state {polyStructs = Map.insert fName (initPolyType fScheme fDef) pSs}

createPolyUnion :: Id -> Scheme -> CExtDecl -> IState ()
createPolyUnion fName fScheme fDef = do
    state@InstantiateMonad{polyUnions = pUs} <- get
    put state {polyUnions = Map.insert fName (initPolyType fScheme fDef) pUs}

createPolyEnum :: Id -> Scheme -> CExtDecl -> IState ()
createPolyEnum fName fScheme fDef = do
    state@InstantiateMonad{polyEnums = pEs} <- get
    put state {polyEnums = Map.insert fName (initPolyType fScheme fDef) pEs}

createClassPolyType :: Id -> Id -> Scheme -> CExtDecl -> IState ()
createClassPolyType cName fName fScheme fDef = do
    state@InstantiateMonad{polyTypes = pTs} <- get
    put state {polyTypes = Map.insert fName (initClassPolyType cName fScheme fDef) pTs}

addPTypeInstance :: Id -> Type -> CExtDecl -> IState ()
addPTypeInstance fName iType iDef = do
    state@InstantiateMonad{polyTypes = pTs} <- get
    put state
      { polyTypes = Map.adjust
          (\pType ->
            pType{pTypeDefinitions = Map.insert iType iDef $ pTypeDefinitions pType}
          )
          fName
          pTs
      }

{- |
  Takes the `Type` needle we want to replace,
  then the `Type` we want to replace it with
  and then the `Type` haystack
-}
replaceType :: Type -> Type -> Type -> Type
replaceType n t (TAp t1 t2) = TAp (replaceType n t t1) (replaceType n t t2)
replaceType n t h
  | n == h    = t
  | otherwise = h

replaceGen :: Id -> [Kind] -> Type -> Type
replaceGen name kinds t = flip foldl t
  (\a (kind, num) ->
    replaceType
      (TGen num)
      (TVar . flip Tyvar kind $ "@TV" ++ name ++ "_par:" ++ show num)
      a
  )
  (zip kinds [0..])

variablizePolyType :: Id -> IState Scheme
variablizePolyType name = do
  name' <- polyAnonRename name
  InstantiateMonad{polyTypes = pTs} <- get
  let
    (Forall kinds (cs :=> t)) = pTypeScheme (pTs Map.! name)
    t' = replaceGen name' kinds t
  return $ Forall [] ([IsIn cId (replaceGen name' kinds cT) | IsIn cId cT <-cs] :=> t')

polyAnonRename :: Id -> IState Id
polyAnonRename id = do
  state@InstantiateMonad{polyAnonNumber = pAN} <- get
  put state{polyAnonNumber = pAN + 1}
  return $ id ++ show pAN

addPolyTypeInstance :: Id -> Id -> IState ()
addPolyTypeInstance pId iId = do
  state@InstantiateMonad{polyTypes = pTs} <- get
  put state
    { polyTypes = Map.adjust (\pType -> pType{pTypeInstances = iId `Set.insert` pTypeInstances pType}) pId pTs
    }

class ReplacePolyTypes a where
  replacePolyTypes :: a -> IState (a, Map.Map Id Id)

instance ReplacePolyTypes CExtDecl where  -- TODO: I think this needs some polish
  replacePolyTypes (CHMFDefExt (CHMFunDef chmHead (CFunDef cDeclSpecs cDeclr cDecls cStmt a) b)) = do
    replaceStmt <- replacePolyTypes cStmt
    let (cStmt', mapStmt) = replaceStmt
    return (CHMFDefExt (CHMFunDef chmHead (CFunDef cDeclSpecs cDeclr cDecls cStmt' a) b), mapStmt)
  replacePolyTypes (CFDefExt (CFunDef cDeclSpecs cDeclr cDecls cStmt a)) = do
    replaceStmt <- replacePolyTypes cStmt
    let (cStmt', mapStmt) = replaceStmt
    return (CFDefExt (CFunDef cDeclSpecs cDeclr cDecls cStmt' a), mapStmt)
  replacePolyTypes cDeclExt@CDeclExt{} = return (cDeclExt, Map.empty)
  replacePolyTypes a = error $ "non-exhaustive for " ++ show a

instance ReplacePolyTypes CStat where
  replacePolyTypes stmt@CLabel{} = return (stmt, Map.empty)
  replacePolyTypes (CCase cExpr cStat a) = do
    (cExpr', exprMap) <- replacePolyTypes cExpr
    (cStat', statMap) <- replacePolyTypes cStat
    return
      ( CCase cExpr' cStat' a
      , exprMap `Map.union` statMap
      )
  replacePolyTypes CCases{} = return $ error "case ranges not yet supported"  -- TODO: do cases
  replacePolyTypes (CDefault cStat a) = do
    (cStat', statMap) <- replacePolyTypes cStat
    return (CDefault cStat' a, statMap)
  replacePolyTypes (CExpr (Just cExpr) a) = do
    (cExpr', exprMap) <- replacePolyTypes cExpr
    return (CExpr (Just cExpr') a, exprMap)
  replacePolyTypes cExpr@(CExpr Nothing _) = return (cExpr, Map.empty)
  replacePolyTypes (CCompound labels blockItems a) = do
    (blockItems', itemsMap) <- replacePolyTypes blockItems
    return (CCompound labels blockItems' a, itemsMap)
  replacePolyTypes (CIf cExpr cThen (Just cElse) a) = do
    (cExpr', exprMap) <- replacePolyTypes cExpr
    (cThen', thenMap) <- replacePolyTypes cThen
    (cElse', elseMap) <- replacePolyTypes cElse
    return
      ( CIf cExpr' cThen' (Just cElse') a
      , exprMap `Map.union` thenMap `Map.union` elseMap
      )
  replacePolyTypes (CIf cExpr cThen Nothing a) = do
    (cExpr', exprMap) <- replacePolyTypes cExpr
    (cThen', thenMap) <- replacePolyTypes cThen
    return
      ( CIf cExpr' cThen' Nothing a
      , exprMap `Map.union` thenMap
      )
  replacePolyTypes (CSwitch cExpr cStat a) = do
    (cExpr', exprMap) <- replacePolyTypes cExpr
    (cStat', statMap) <- replacePolyTypes cStat
    return
      ( CSwitch cExpr' cStat' a
      , exprMap `Map.union` statMap
      )
  replacePolyTypes (CWhile cExpr cStat doWhile a) = do
    (cExpr', exprMap) <- replacePolyTypes cExpr
    (cStat', statMap) <- replacePolyTypes cStat
    return
      ( CWhile cExpr' cStat' doWhile a
      , exprMap `Map.union` statMap
      )
  replacePolyTypes CFor{} = return $ error "for is not yet supported"  -- TODO: do for
  replacePolyTypes cGoto@(CGoto _ _) = return (cGoto, Map.empty)
  replacePolyTypes cGotoPtr@(CGotoPtr _ _) = return (cGotoPtr, Map.empty)  -- TODO: well this is not right, right?
  replacePolyTypes cCont@(CCont _) = return (cCont, Map.empty)
  replacePolyTypes cBreak@(CBreak _) = return (cBreak, Map.empty)
  replacePolyTypes (CReturn (Just cExpr) a) = do
    (cExpr', exprMap) <- replacePolyTypes cExpr
    return (CReturn (Just cExpr') a, exprMap)
  replacePolyTypes cAsm@(CAsm _ _) = return (cAsm, Map.empty)  -- TODO: todo or not todo

instance ReplacePolyTypes CBlockItem where  -- TODO:
  replacePolyTypes (CBlockStmt cStat) = do
    (cStat', statMap) <- replacePolyTypes cStat
    return (CBlockStmt cStat', statMap)
  replacePolyTypes (CBlockDecl cDeclr) = do
    (cDeclr', declrMap) <- replacePolyTypes cDeclr
    return (CBlockDecl cDeclr', declrMap)

instance ReplacePolyTypes CDecl where
  replacePolyTypes (CDecl cDeclSpecs cDeclDecls a) = do
    (cDeclSpecs', declSpecsMap) <- replacePolyTypes cDeclSpecs
    (cDeclDecls', declDeclsMap) <- replacePolyTypes cDeclDecls
    return
      ( CDecl cDeclSpecs' cDeclDecls' a
      , declSpecsMap `Map.union` declDeclsMap
      )

instance ReplacePolyTypes CDeclDecl where
  replacePolyTypes (mDeclr, mInit, mExpr) = do
    (mDeclr', declrMap) <- replacePolyTypes mDeclr
    (mInit', initMap) <- replacePolyTypes mInit
    (mExpr', exprMap) <- replacePolyTypes mExpr
    return
      ( (mDeclr', mInit', mExpr')
      , declrMap `Map.union` initMap `Map.union` exprMap
      )

instance ReplacePolyTypes CInit where
  replacePolyTypes (CInitExpr cExpr a) = do
    (cExpr', exprMap) <- replacePolyTypes cExpr
    return (CInitExpr cExpr' a, exprMap)
  replacePolyTypes (CInitList cInitList a) = do
    (cInitList', initListMap) <- replacePolyTypes cInitList
    return (CInitList cInitList' a, initListMap)

instance ReplacePolyTypes CInitListItem where
  replacePolyTypes (cDesigs, cInit) = do
    (cDesigs', desigsMap) <- replacePolyTypes cDesigs
    (cInit', initMap) <- replacePolyTypes cInit
    return
      ( (cDesigs', cInit')
      , desigsMap `Map.union` initMap
      )

instance ReplacePolyTypes CDesignator where
  replacePolyTypes (CArrDesig cExpr a) = do
    (cExpr', exprMap) <- replacePolyTypes cExpr
    return (CArrDesig cExpr' a, exprMap)
  replacePolyTypes cMemberDesig@CMemberDesig{} =
    return (cMemberDesig, Map.empty)
  replacePolyTypes (CRangeDesig cExpr1 cExpr2 a) = do
    (cExpr1', expr1Map) <- replacePolyTypes cExpr1
    (cExpr2', expr2Map) <- replacePolyTypes cExpr2
    return
      ( CRangeDesig cExpr1' cExpr2' a
      , expr1Map `Map.union` expr2Map
      )

instance ReplacePolyTypes CDeclSpec where
  replacePolyTypes (CTypeSpec cTypeSpec) = do
    (cTypeSpec', typeSpecMap) <- replacePolyTypes cTypeSpec
    return (CTypeSpec cTypeSpec', typeSpecMap)
  replacePolyTypes (CAlignSpec cAlignSpec) = do
    (cAlignSpec', alignSpecMap) <- replacePolyTypes cAlignSpec
    return (CAlignSpec cAlignSpec', alignSpecMap)
  replacePolyTypes a = return (a, Map.empty)

instance ReplacePolyTypes CTypeSpec where
  replacePolyTypes cTypeDef@(CTypeDef (Ident sId _ pos) a) = do
    pTs <- gets polyTypes
    if sId `Map.member` pTs
      then do
        sId' <- polyAnonRename sId
        return (CTypeDef (Ident sId' (quad sId') pos) a, Map.singleton sId' sId)
      else return (cTypeDef, Map.empty)
  replacePolyTypes (CTypeOfExpr cExpr a) = do
    (cExpr', exprMap) <- replacePolyTypes cExpr
    return (CTypeOfExpr cExpr' a, exprMap)
  replacePolyTypes (CTypeOfType cDeclr a) = do
    (cDeclr', exprMap) <- replacePolyTypes cDeclr
    return (CTypeOfType cDeclr' a, exprMap)
  replacePolyTypes (CAtomicType cDeclr a) = do
    (cDeclr', exprMap) <- replacePolyTypes cDeclr
    return (CAtomicType cDeclr' a, exprMap)
  replacePolyTypes a = return (a, Map.empty)

instance ReplacePolyTypes CAlignSpec where
  replacePolyTypes (CAlignAsType cDeclr a) = do
    (cDeclr', exprMap) <- replacePolyTypes cDeclr
    return (CAlignAsType cDeclr' a, exprMap)
  replacePolyTypes (CAlignAsExpr cExpr a) = do
    (cExpr', exprMap) <- replacePolyTypes cExpr
    return (CAlignAsExpr cExpr' a, exprMap)

instance ReplacePolyTypes CDeclr where
  replacePolyTypes (CDeclr mIdent cDerivedDeclrs mStrLit cAttrs a) = do
    (cDerivedDeclrs', derivedDeclrsMap) <- replacePolyTypes cDerivedDeclrs
    (cAttrs', attrsMap) <- replacePolyTypes cAttrs
    return
      ( CDeclr mIdent cDerivedDeclrs' mStrLit cAttrs' a
      , derivedDeclrsMap `Map.union` attrsMap
      )
  replacePolyTypes (CHMDeclr cDeclr chmPars a ) = error "not yet done"  -- TODO

instance ReplacePolyTypes CAttr where
  replacePolyTypes (CAttr ident cExprs a) = do
    (cExprs', exprsMap) <- replacePolyTypes cExprs
    return (CAttr ident cExprs' a, exprsMap)

instance ReplacePolyTypes CDerivedDeclr where
  replacePolyTypes (CFunDeclr (Left idents) cAttrs a) =
    error "not supporting old-style functions"  -- TODO: support old-style functions
  replacePolyTypes (CFunDeclr (Right (cDeclrs, varArgs)) cAttrs a) = do
    (cDeclrs', declrsMap) <- replacePolyTypes cDeclrs
    (cAttrs', attrsMap) <- replacePolyTypes cAttrs
    return
      ( CFunDeclr (Right (cDeclrs', varArgs)) cAttrs' a
      , declrsMap `Map.union` attrsMap
      )
  replacePolyTypes a = return (a, Map.empty)

instance ReplacePolyTypes CExpr where
  replacePolyTypes (CComma cExprs a) = do
    (cExprs', exprsMap) <- replacePolyTypes cExprs
    return (CComma cExprs' a, exprsMap)
  replacePolyTypes (CAssign assOp lExpr rExpr a) = do
    (lExpr', lMap) <- replacePolyTypes lExpr
    (rExpr', rMap) <- replacePolyTypes rExpr
    return (CAssign assOp lExpr' rExpr' a, lMap `Map.union` rMap)
  replacePolyTypes (CCond cExpr (Just cThen) cElse a) = do
    (cExpr', exprMap) <- replacePolyTypes cExpr
    (cThen', thenMap) <- replacePolyTypes cThen
    (cElse', elseMap) <- replacePolyTypes cElse
    return
      ( CCond cExpr' (Just cThen') cElse' a
      , exprMap `Map.union` thenMap `Map.union` elseMap
      )
  replacePolyTypes (CBinary binOp cLeft cRight a) = do
    (cLeft', leftMap) <- replacePolyTypes cLeft
    (cRight', rightMap) <- replacePolyTypes cRight
    return
      ( CBinary binOp cLeft' cRight' a
      , leftMap `Map.union` rightMap
      )
  -- TODO: CCast
  replacePolyTypes (CUnary unOp cExpr a) = do
    (cExpr', exprMap) <- replacePolyTypes cExpr
    return (CUnary unOp cExpr' a, exprMap)
  replacePolyTypes (CSizeofExpr cExpr a) = do
    (cExpr', exprMap) <- replacePolyTypes cExpr
    return (CSizeofExpr cExpr' a, exprMap)
  -- TODO: CSizeofType
  replacePolyTypes (CAlignofExpr cExpr a) = do
    (cExpr', exprMap) <- replacePolyTypes cExpr
    return (CAlignofExpr cExpr' a, exprMap)
  -- TODO: CAlignofType
  replacePolyTypes (CComplexReal cExpr a) = do
    (cExpr', exprMap) <- replacePolyTypes cExpr
    return (CComplexReal cExpr' a, exprMap)
  replacePolyTypes (CComplexImag cExpr a) = do
    (cExpr', exprMap) <- replacePolyTypes cExpr
    return (CComplexImag cExpr' a, exprMap)
  replacePolyTypes (CCall cExpr cExprs a) = do
    (cExpr', exprMap) <- replacePolyTypes cExpr
    (cExprs', exprsMap) <- replacePolyTypes cExprs
    return (CCall cExpr' cExprs' a, exprMap `Map.union` exprsMap)
  replacePolyTypes (CMember cExpr ident deref a) = do
    (cExpr', exprMap) <- replacePolyTypes cExpr
    return (CMember cExpr' ident deref a, exprMap)
  replacePolyTypes cVar@(CVar (Ident vId _ pos) a) = do
    pTs <- gets polyTypes
    if vId `Map.member` pTs
      then do
        vId' <- polyAnonRename vId
        return (CVar (Ident vId' (quad vId') pos) a, Map.singleton vId' vId)
      else return (cVar, Map.empty)
  replacePolyTypes cConst@(CConst _) = return (cConst, Map.empty)
  -- TODO: CCompoundLit
  -- TODO: CGenericSelection
  replacePolyTypes (CStatExpr cStat a) = do
    (cStat', statMap) <- replacePolyTypes cStat
    return (CStatExpr cStat' a, statMap)
  replacePolyTypes cLabAddrExpr@(CLabAddrExpr _ _) = return (cLabAddrExpr, Map.empty)
  -- TODO: CBuiltinExpr

quad                 :: String -> Int
quad (c1:c2:c3:c4:s)  = ((ord c4 * bits21
                          + ord c3 * bits14
                          + ord c2 * bits7
                          + ord c1)
                         `mod` bits28)
                        + (quad s `mod` bits28)
quad [c1, c2, c3] = ord c3 * bits14 + ord c2 * bits7 + ord c1
quad [c1, c2    ] = ord c2 * bits7 + ord c1
quad [c1        ] = ord c1
quad [          ] = 0

bits7 :: Int
bits7  = 2^(7::Int)
bits14 :: Int
bits14 = 2^(14::Int)
bits21 :: Int
bits21 = 2^(21::Int)
bits28 :: Int
bits28 = 2^(28::Int)

instance ReplacePolyTypes a => ReplacePolyTypes [a] where
  replacePolyTypes as = do
    as' <- traverse replacePolyTypes as
    return (fst <$> as', foldl Map.union Map.empty (snd <$> as'))

instance ReplacePolyTypes a => ReplacePolyTypes (Maybe a) where
  replacePolyTypes Nothing = return (Nothing, Map.empty)
  replacePolyTypes (Just a) = do
    (a', aMap) <- replacePolyTypes a
    return (Just a', aMap)

instantiate :: CExtDecl -> Scheme -> IState [CExtDecl]
instantiate extFunDef scheme = do
  syncScopes
  (extFunDef', polyMap) <- replacePolyTypes extFunDef
  expls <- sequence
    [ do
        scheme' <- variablizePolyType real
        return
          ( var
          , scheme'
          , []
          )
    | (var, real) <- Map.toList polyMap
    ]
  tState <- gets transformState
  let (_, tState') = runState (traverse storeName $ Map.keys polyMap) tState
  modify (\state -> state{transformState = tState'})
  as <- parseReSchemedVirtual scheme extFunDef' (expls, [])
  state'' <- get
  put state''{transformState = tState}
  children <- concat <$> sequence
    [ case name' `Map.lookup` polyMap of
        (Just name) -> do
          pTs <- gets polyTypes
          let
            pType = pTs Map.! name
            mangledName = "__" ++ name ++ mangle scheme'
          if mangledName `Set.member` pTypeInstances pType
            then return []
            else addPolyTypeInstance name mangledName >> instantiate (pTypeDefinition pType) scheme'
        Nothing -> return []
    | (name' :>: scheme') <- as
    ]
  let
    funName = getCName extFunDef'
    tVarMap = foldl Map.union Map.empty
      [ if and (zipWith (==) name' funName)
          then drop (length funName + 1) name' `Map.singleton` scheme'
          else name' `Map.singleton` scheme'
      | (name' :>: scheme') <- as
      ]
    -- TODO
  let extFunDef'' = replaceTVars (tVarMap, polyMap) extFunDef'
  (children ++) . pure  <$> rewrite extFunDef'' scheme

class ReplaceTVars a where
  replaceTVars :: (Map.Map Id Scheme, Map.Map Id Id) -> a -> a

instance ReplaceTVars CExtDecl where
  replaceTVars as (CHMFDefExt chmFunDef) =
    CHMFDefExt (replaceTVars as chmFunDef)
  replaceTVars as (CFDefExt cFunDef) =
    CFDefExt (replaceTVars as cFunDef)
  replaceTVars as (CDeclExt cDecl) =
    CDeclExt (replaceTVars as cDecl)

instance ReplaceTVars CHMFunDef where
  replaceTVars as (CHMFunDef chmHead cFunDef a) =
    CHMFunDef chmHead (replaceTVars as cFunDef) a

instance ReplaceTVars CFunDef where
  replaceTVars as (CFunDef specs cDeclr decls stmt a) =
    CFunDef
      (replaceTVars as specs)
      (replaceTVars as cDeclr)
      (replaceTVars as decls)
      (replaceTVars as stmt)
      a

instance ReplaceTVars CDeclSpec where
  replaceTVars as (CTypeSpec cTypeSpec) =
    CTypeSpec (replaceTVars as cTypeSpec)
  replaceTVars as (CAlignSpec cAlignSpec) =
    CAlignSpec (replaceTVars as cAlignSpec)  -- TODO
  replaceTVars _ a = a

schemeToMono :: Scheme -> Id
schemeToMono = ('_' :) . mangle  -- TODO

instance ReplaceTVars CTypeSpec where
  replaceTVars as cTypeDef@(CTypeDef (Ident sId a b) c) =
    case sId `Map.lookup` fst as of
      (Just scheme) ->
        let monoType = schemeToMono scheme  -- TODO
        in CTypeDef (Ident monoType (quad monoType) b) c
      Nothing -> cTypeDef
  replaceTVars as (CTypeOfExpr cExpr a) =
    CTypeOfExpr (replaceTVars as cExpr) a
  replaceTVars as (CTypeOfType cDeclr a) =
    CTypeOfType (replaceTVars as cDeclr) a
  replaceTVars as (CAtomicType cDeclr a) =
    CAtomicType (replaceTVars as cDeclr) a
  replaceTVars _ a = a

instance ReplaceTVars CAlignSpec where
  replaceTVars as (CAlignAsType cDeclr a) =
    CAlignAsType
      (replaceTVars as cDeclr)
      a
  replaceTVars as (CAlignAsExpr cExpr a) =
    CAlignAsExpr
      (replaceTVars as cExpr)
      a

instance ReplaceTVars CDeclr where
  replaceTVars as (CDeclr mIdent cDerivedDeclrs mStrLit cAttrs a) =
    CDeclr
      mIdent
      (replaceTVars as cDerivedDeclrs)
      mStrLit
      (replaceTVars as cAttrs)
      a
  replaceTVars as (CHMDeclr cDeclr chmPars a) =
    CHMDeclr
      (replaceTVars as cDeclr)
      (replaceTVars as chmPars)
      a

instance ReplaceTVars CDerivedDeclr where
  replaceTVars as (CFunDeclr (Left idents) cAttrs a) =
    error "not supporting old-style functions"  -- TODO: support old-style functions
  replaceTVars as (CFunDeclr (Right (cDeclrs, varArgs)) cAttrs a) =
    CFunDeclr
      (Right (replaceTVars as cDeclrs, varArgs))
      (replaceTVars as cAttrs)
      a
  -- CPtrDeclr and CArrDeclr
  replaceTVars _ a = a

instance ReplaceTVars CHMParams where
  replaceTVars as (CHMParams chmTypes a) =
    CHMParams (replaceTVars as chmTypes) a

instance ReplaceTVars CHMT where
  replaceTVars as (CHMCType cDeclSpecs a) =
    CHMCType (replaceTVars as cDeclSpecs) a
  replaceTVars as (CHMCDeclType cDeclr a) =
    CHMCDeclType (replaceTVars as cDeclr) a
  replaceTVars as (CHMParType chmType chmPars a) =
    CHMParType
      (replaceTVars as chmType)
      (replaceTVars as chmPars)
      a

type CDeclDecl = (Maybe CDeclr, Maybe CInit, Maybe CExpr)

instance ReplaceTVars CDecl where
  replaceTVars as (CDecl cDeclSpecs cDeclDecls a) =
    CDecl
      (replaceTVars as cDeclSpecs)
      (replaceTVars as cDeclDecls)
      a

instance ReplaceTVars CDeclDecl where
  replaceTVars as (mDeclr, mInit, mExpr) =
    ( replaceTVars as mDeclr
    , replaceTVars as mInit
    , replaceTVars as mExpr
    )

instance ReplaceTVars CInit where
  replaceTVars as (CInitExpr cExpr a) =
    CInitExpr (replaceTVars as cExpr) a
  replaceTVars as (CInitList cInitList a) =
    CInitList (replaceTVars as cInitList) a

type CInitListItem = ([CDesignator], CInit)

instance ReplaceTVars CInitListItem where
  replaceTVars as (cDesignators, cInit) =
    (replaceTVars as cDesignators, replaceTVars as cInit)

instance ReplaceTVars CDesignator where
  replaceTVars as (CArrDesig cExpr a) =
    CArrDesig (replaceTVars as cExpr) a
  replaceTVars as cMemberDesig@CMemberDesig{} = cMemberDesig
  replaceTVars as (CRangeDesig cExpr1 cExpr2 a) =
    CRangeDesig
      (replaceTVars as cExpr1)
      (replaceTVars as cExpr2)
      a

instance ReplaceTVars CStat where
  replaceTVars as (CLabel ident cStmt cAttrs a) =
    CLabel ident (replaceTVars as cStmt) (replaceTVars as cAttrs) a
  replaceTVars as (CCase cExpr cStmt a) =
    CCase (replaceTVars as cExpr) (replaceTVars as cStmt) a
  replaceTVars as (CCases cExpr1 cExpr2 cStmt a) =
    CCases
      (replaceTVars as cExpr1)
      (replaceTVars as cExpr2)
      (replaceTVars as cStmt)
      a
  replaceTVars as (CDefault cStmt a) =
    CDefault (replaceTVars as cStmt) a
  replaceTVars as (CExpr mExpr a) =
    CExpr (replaceTVars as mExpr) a
  replaceTVars as (CCompound idents cBlockItems a) =
    CCompound idents (replaceTVars as cBlockItems) a
  replaceTVars as (CIf cExpr cStmt mStmt a) =
    CIf
      (replaceTVars as cExpr)
      (replaceTVars as cStmt)
      (replaceTVars as mStmt)
      a
  replaceTVars as CFor{} = error "do later"  -- TODO
  replaceTVars as cGoto@CGoto{} = cGoto
  replaceTVars as (CGotoPtr cExpr a) =
    CGotoPtr (replaceTVars as cExpr) a
  replaceTVars as cCont@CCont{} = cCont
  replaceTVars as cBreak@CBreak{} = cBreak
  replaceTVars as (CReturn mExpr a) =
    CReturn
      (replaceTVars as mExpr)
      a
  replaceTVars as cAsm@CAsm{} = cAsm  -- TODO

instance ReplaceTVars CBlockItem where
  replaceTVars as (CBlockStmt cStmt) = CBlockStmt (replaceTVars as cStmt)
  replaceTVars as (CBlockDecl cDeclr) = CBlockDecl (replaceTVars as cDeclr)
  replaceTVars as (CNestedFunDef cFunDef) = CNestedFunDef (replaceTVars as cFunDef)

instance ReplaceTVars CAttr where
  replaceTVars as (CAttr ident cExprs a) =
    CAttr ident (replaceTVars as cExprs) a

instance ReplaceTVars CExpr where
  replaceTVars as (CComma cExprs a) =
    CComma (replaceTVars as cExprs) a
  replaceTVars as (CAssign assOp cExpr1 cExpr2 a) =
    CAssign
      assOp
      (replaceTVars as cExpr1)
      (replaceTVars as cExpr2)
      a
  replaceTVars as (CCond cExpr1 mExpr cExpr2 a) =
    CCond
      (replaceTVars as cExpr1)
      (replaceTVars as mExpr)
      (replaceTVars as cExpr2)
      a
  replaceTVars as (CBinary binOp cExpr1 cExpr2 a) =
    CBinary
      binOp
      (replaceTVars as cExpr1)
      (replaceTVars as cExpr2)
      a
  replaceTVars as (CCast cDeclr cExpr a) =
    CCast
      (replaceTVars as cDeclr)
      (replaceTVars as cExpr)
      a
  replaceTVars as (CUnary unOp cExpr a) =
    CUnary
      unOp
      (replaceTVars as cExpr)
      a
  replaceTVars as (CSizeofExpr cExpr a) =
    CSizeofExpr (replaceTVars as cExpr) a
  replaceTVars as (CSizeofType cDeclr a) =
    CSizeofType (replaceTVars as cDeclr) a
  replaceTVars as (CAlignofExpr cExpr a) =
    CAlignofExpr (replaceTVars as cExpr) a
  replaceTVars as (CAlignofType cDeclr a) =
    CAlignofType (replaceTVars as cDeclr) a
  replaceTVars as (CComplexReal cExpr a) =
    CComplexReal (replaceTVars as cExpr) a
  replaceTVars as (CComplexImag cExpr a) =
    CComplexImag (replaceTVars as cExpr) a
  replaceTVars as (CIndex cExpr1 cExpr2 a) =
    CIndex
      (replaceTVars as cExpr1)
      (replaceTVars as cExpr2)
      a
  replaceTVars as (CCall cExpr cExprs a) =
    CCall
      (replaceTVars as cExpr)
      (replaceTVars as cExprs)
      a
  replaceTVars as (CMember cExpr ident deref a) =
    CMember (replaceTVars as cExpr) ident deref a
  replaceTVars as cVar@(CVar (Ident sId _ pos) a) =
    case sId `Map.lookup` fst as of
      Just scheme ->
        let name = "__" ++ (snd as Map.! sId) ++ mangle scheme
        in CVar (Ident name (quad name) pos) a
      Nothing -> cVar
  replaceTVars as cConst@CConst{} = cConst
  replaceTVars as (CCompoundLit cDeclr cInitList a) =
    CCompoundLit
      (replaceTVars as cDeclr)
      (replaceTVars as cInitList)
      a
  replaceTVars as CGenericSelection{} =
    error "not supporting c generic selections"  -- TODO: maybe yes
  replaceTVars as (CStatExpr cStmt a) =
    CStatExpr
      (replaceTVars as cStmt)
      a
  replaceTVars as cLabAddrExpr@CLabAddrExpr{} = cLabAddrExpr
  replaceTVars as CBuiltinExpr{} =
    error "not supporting builinThing"  -- TODO: maybe do support

instance ReplaceTVars b => ReplaceTVars [b] where
  replaceTVars as bs = replaceTVars as <$> bs

instance ReplaceTVars b => ReplaceTVars (Maybe b) where
  replaceTVars as m = replaceTVars as <$> m

renameFunDef :: Id -> CFunDef -> CFunDef
renameFunDef name' (CFunDef a (CDeclr (Just (Ident sId _ pos)) b c d e) f g h) =
  let new_ident = Ident name' (quad name') pos
  in CFunDef a (CDeclr (Just new_ident) b c d e) f g h

class GetFunDef a where
  getFunDef :: a -> CFunDef

instance GetFunDef CExtDecl where
  getFunDef (CFDefExt cFunDef) = cFunDef
  getFunDef (CHMFDefExt chmFunDef) = getFunDef chmFunDef

instance GetFunDef CHMFunDef where
  getFunDef (CHMFunDef _ cFunDef _) = cFunDef

rewrite :: CExtDecl -> Scheme -> IState CExtDecl  -- TODO
rewrite cExtDecl@CFDefExt{} _ = return cExtDecl
rewrite
  cExtDecl@( CHMFDefExt
      ( CHMFunDef
          chmHead
          funDef@( CFunDef
              _
              (CDeclr (Just (Ident name _ _)) _ _ _ _)
              _
              _
              _
          )
          _
      )
  )
  scheme = return . CFDefExt $ renameFunDef ("__" ++ name ++ mangle scheme) funDef  -- TODO

rewrite cExtDecl scheme@(Forall [] (cs :=> t)) = do
  let name = getCName cExtDecl
  pType <- gets ((Map.! name) . polyTypes)
  let
    Just cId = pTypeClass pType
    Just (IsIn _ cT) = List.find (\(IsIn cId' t') -> cId' == cId) cs
    substs = catMaybes
      [ if c == cT
           -- || not (null . runTI $ mgu cT c)
          then Just def
          else Nothing
      | (c, def) <- Map.toList (pTypeDefinitions pType)
      ]
  case substs of
    [] -> error "cannot create the instance"
    [iDef] -> return . CFDefExt $ renameFunDef ("__" ++ name ++ mangle scheme) (getFunDef iDef)
    _ -> error "I don't know yet"  -- TODO

parseReSchemedVirtual :: Scheme -> CExtDecl -> BindGroup -> IState [Assump]
parseReSchemedVirtual scheme cExtDecl bindGroup = do
  InstantiateMonad{transformState = tS, parsedAssumps = pAs} <- get
  let
    (as, tS') = flip runState tS $
      case cExtDecl of
        CFDefExt{} -> transform cExtDecl >>= typeInfer pAs . (bindGroup:)
        CHMFDefExt (CHMFunDef (CHMHead tVars _ _) _ _) -> do
          cExtDecl' <- transformCHMFunDef cExtDecl
          let [([(name, polyScheme, alts)], []), (parExpls, [])] = cExtDecl'
          typeInfer pAs
            [ bindGroup
            , ( parExpls ++ [ ("__" ++ name ++ mangle scheme
                  , scheme
                  , alts
                  )
                ]
              , []
              )
            ]
        CDeclExt{} -> transform cExtDecl >>= typeInfer pAs . (bindGroup:)
  return as

syncScopes :: IState ()
syncScopes = do
  state@InstantiateMonad{transformState = tS} <- get
  put state {lastScopeCopy = lastScope tS}

runTState :: TState a -> IState a
runTState a = do
  state@InstantiateMonad{transformState = tS} <- get
  let (a', tS') = runState a tS
  put state{transformState = tS'}
  return a'

parse :: Transform a => a -> IState [Assump]
parse a = do
  state@InstantiateMonad{transformState = tS, parsedAssumps = pAs} <- get
  let (as, tS') = runState (transform a >>= typeInfer pAs) tS
  put state
    { transformState = tS'
    , parsedAssumps = as ++ pAs
    }
  return as

mangleScheme :: Scheme -> Id
mangleScheme (Forall [] (cs :=> t)) = mangleType t

builtinTypes :: Map.Map Id Id
builtinTypes = Map.fromList
  [ (tCharId, "char")
  , (tIntId, "int")
  , (tFloatId, "float")
  , (tDoubleId, "double")
  ]

mangleType :: Type -> Id
mangleType (TCon (Tycon id _)) = case id `Map.lookup` builtinTypes of
  Nothing -> "TC" ++ show (length id) ++ id
  Just cName -> cName

mangleType (TAp (TAp tArrow t1) t2) =
  let
    t1' = manglePars t1
    t2' = mangleType t2
  in "TF" ++ show (length t1') ++ t1' ++ show (length t2') ++ t2'

mangleType (TAp t1 t2)
  | t1 == tPointer = let
      t1' = mangleType t2
    in "TP" ++ show (length t1') ++ t1'
  | otherwise = let
      t1' = mangleType t1
      t2' = mangleType t2
    in "TA" ++ show (length t1') ++ t1' ++ show (length t2') ++ t2'

manglePars :: Type -> Id
manglePars TCon{} = ""
manglePars (TAp t1 t2) =
  let
    t1' = manglePars t1
    t2' = mangleType t2
  in t1' ++ t2'

class Mangle a where
  mangle :: a -> Id

instance Mangle Type where
  mangle t = "_" ++ mangleType t

instance Mangle Scheme where
  mangle s = "_" ++ mangleScheme s
