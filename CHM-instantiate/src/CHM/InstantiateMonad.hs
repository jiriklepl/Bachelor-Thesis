{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module CHM.InstantiateMonad where

import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.Set as Set
import qualified Data.List as List
import qualified Data.Sequence as Seq
import Data.Char
import Data.Maybe

import qualified Data.ByteString.Char8 as T

import Debug.Trace

import Language.C.Syntax
import Language.C.Data
import Language.C.Data.Ident (Ident(..))
import Language.C.Data.Error

import TypingHaskellInHaskell hiding (modify)
import CHM.Transform

type IState = State InstantiateMonad

-- | Remembers the main definition (or definitions if is classed) and list of instances
data PolyType = PolyType
  { pTypeDefinition  :: CExtDecl
    -- ^ The C definition of the PolyType
  , pTypeDefinitions :: Map.Map Type CExtDecl
    -- ^ Multiple definitions in case there are instanced definitions
  , pTypeClass       :: Maybe Id
    -- ^ If it is a method, it remembers 'Just' the class, otherwise 'Nothing'
  , pTypeScheme      :: Scheme
    -- ^ Scheme of the template
  , pTypeInstances   :: Set.Set Id
    -- ^ Set of all instances
  }
  deriving (Show)

data InstantiateMonad = InstantiateMonad
  { parsedAssumps    :: Map.Map Id Scheme
  , transformState   :: TransformMonad
  , lastScopeCopy    :: Int
  , polyTypes        :: Map.Map Id PolyType
  , polyStructUnions :: Map.Map Id PolyType
  , polyEnums        :: Map.Map Id PolyType
  , schemeInstances  :: Set.Set Id
  , polyAnonNumber   :: Int
  , polyMaps         :: [Map.Map Id Id]
  , cProgram         :: Seq.Seq CExtDecl
  }


-- | Creates the PolyType just with the scheme and the C definition
initPolyType :: Scheme -> CExtDecl -> PolyType
initPolyType scheme def = PolyType
  { pTypeDefinition = def
  , pTypeDefinitions = mempty
  , pTypeClass = Nothing
  , pTypeScheme = scheme
  , pTypeInstances = mempty
  }

initClassPolyType :: Id -> Scheme -> CExtDecl -> PolyType
initClassPolyType cName fScheme fDef =
  (initPolyType fScheme fDef){pTypeClass = Just cName}

initInstantiateMonad :: InstantiateMonad
initInstantiateMonad = InstantiateMonad
  { parsedAssumps    = mempty
  , transformState   = initTransformMonad
  , lastScopeCopy    = 0
  , polyTypes        = mempty
  , polyStructUnions = mempty
  , polyEnums        = mempty
  , schemeInstances  = mempty
  , polyAnonNumber   = 0
  , polyMaps         = []
  , cProgram         = mempty
  }

dUnderScore = T.pack "__" :: Id

pushPolyMaps, pullPolyMaps :: IState ()
pushPolyMaps = modify (\state -> state{polyMaps = mempty : polyMaps state})
pullPolyMaps = modify (\state -> state{polyMaps = tail $ polyMaps state})

enqueueExtDecl :: CExtDecl -> IState ()
enqueueExtDecl cExtDecl =
  modify (\state -> state{cProgram = cProgram state Seq.|> cExtDecl})

createPolyType :: Id -> Scheme -> CExtDecl -> IState ()
createPolyType fName fScheme fDef = do
    state@InstantiateMonad{polyTypes = pTs} <- get
    put state {polyTypes = Map.insert fName (initPolyType fScheme fDef) pTs}

createPolyStruct :: Id -> Scheme -> CExtDecl -> IState ()
createPolyStruct fName fScheme fDef = do
    state@InstantiateMonad{polyStructUnions = pSs} <- get
    put state {polyStructUnions = Map.insert fName (initPolyType fScheme fDef) pSs}

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
replaceGen name kinds t = foldl
  (\a (kind, num) ->
    replaceType
      (TGen num)
      (TVar . flip Tyvar kind $ T.concat [T.pack "@TV" , name , T.pack "_par:" , T.pack $ show num])
      a
  )
  t
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
  pAN <- gets polyAnonNumber
  modify (\state -> state{polyAnonNumber = pAN + 1})
  return $ id <> T.pack (show pAN)

addPolyTypeInstance :: Id -> Id -> IState ()
addPolyTypeInstance pId iId = do
  state@InstantiateMonad{polyTypes = pTs} <- get
  put state
    { polyTypes = Map.adjust (\pType -> pType{pTypeInstances = iId `Set.insert` pTypeInstances pType}) pId pTs
    }

class ReplacePolyTypes a where
  replacePolyTypes :: a -> IState a

instance ReplacePolyTypes CExtDecl where
  replacePolyTypes (CHMFDefExt chmFunDef) =
    CHMFDefExt <$> replacePolyTypes chmFunDef
  replacePolyTypes (CFDefExt cFunDef) =
    CFDefExt <$> replacePolyTypes cFunDef
  replacePolyTypes (CHMSDefExt chmStructDef) =
    CHMSDefExt <$> replacePolyTypes chmStructDef
  replacePolyTypes cDeclExt@CDeclExt{} = return cDeclExt

instance ReplacePolyTypes CHMFunDef where
  replacePolyTypes (CHMFunDef chmHead cFunDef a) =
    flip (CHMFunDef chmHead) a <$> replacePolyTypes cFunDef

instance ReplacePolyTypes CFunDef where
  replacePolyTypes (CFunDef cDeclSpecs cDeclr cDecls cStmt a) =
    flip (CFunDef cDeclSpecs cDeclr cDecls) a <$> replacePolyTypes cStmt

instance ReplacePolyTypes CHMStructDef where
  replacePolyTypes (CHMStructDef chmHead cStructUnion a) =
    flip (CHMStructDef chmHead) a <$> replacePolyTypes cStructUnion

instance ReplacePolyTypes CStructUnion where
  replacePolyTypes (CStruct cStructTag mIdent mDecls cAttrs a) = do
    mDecls' <- replacePolyTypes mDecls
    cAttrs' <- replacePolyTypes cAttrs
    return $ CStruct cStructTag mIdent mDecls cAttrs a

instance ReplacePolyTypes CStat where
  replacePolyTypes stmt@CLabel{} = return stmt
  replacePolyTypes (CCase cExpr cStat a) = do
    cExpr' <- replacePolyTypes cExpr
    cStat' <- replacePolyTypes cStat
    return $ CCase cExpr' cStat' a
  replacePolyTypes (CCases lExpr uExpr cStat a) = do
    lExpr' <- replacePolyTypes lExpr
    uExpr' <- replacePolyTypes uExpr
    cStat' <- replacePolyTypes cStat
    return $ CCases lExpr' uExpr' cStat' a
  replacePolyTypes (CDefault cStat a) =
    flip CDefault a <$> replacePolyTypes cStat
  replacePolyTypes (CExpr (Just cExpr) a) =
    flip CExpr a . Just <$> replacePolyTypes cExpr
  replacePolyTypes cExpr@(CExpr Nothing _) = return cExpr
  replacePolyTypes (CCompound labels blockItems a) =
    flip (CCompound labels) a <$> replacePolyTypes blockItems
  replacePolyTypes (CIf cExpr cThen (Just cElse) a) = do
    cExpr' <- replacePolyTypes cExpr
    cThen' <- replacePolyTypes cThen
    cElse' <- replacePolyTypes cElse
    return $ CIf cExpr' cThen' (Just cElse') a
  replacePolyTypes (CIf cExpr cThen Nothing a) = do
    cExpr' <- replacePolyTypes cExpr
    cThen' <- replacePolyTypes cThen
    return $ CIf cExpr' cThen' Nothing a
  replacePolyTypes (CSwitch cExpr cStat a) = do
    cExpr' <- replacePolyTypes cExpr
    cStat' <- replacePolyTypes cStat
    return $ CSwitch cExpr' cStat' a
  replacePolyTypes (CWhile cExpr cStat doWhile a) = do
    cExpr' <- replacePolyTypes cExpr
    cStat' <- replacePolyTypes cStat
    return $ CWhile cExpr' cStat' doWhile a
  replacePolyTypes (CFor eExprDecl mExpr2 mExpr3 cStat a) = do
    eExprDecl' <- replacePolyTypes eExprDecl
    mExpr2' <- replacePolyTypes mExpr2
    mExpr3' <- replacePolyTypes mExpr3
    cStat' <- replacePolyTypes cStat
    return $ CFor eExprDecl' mExpr2' mExpr3' cStat' a
  replacePolyTypes cGoto@(CGoto _ _) = return cGoto
  replacePolyTypes cGotoPtr@(CGotoPtr _ _) = return cGotoPtr
  replacePolyTypes cCont@(CCont _) = return cCont
  replacePolyTypes cBreak@(CBreak _) = return cBreak
  replacePolyTypes (CReturn (Just cExpr) a) =
    flip CReturn a . Just <$> replacePolyTypes cExpr
  replacePolyTypes cAsm@(CAsm _ _) = return cAsm

instance ReplacePolyTypes CBlockItem where
  replacePolyTypes (CBlockStmt cStat) =
    CBlockStmt <$> replacePolyTypes cStat
  replacePolyTypes (CBlockDecl cDeclr) =
    CBlockDecl <$> replacePolyTypes cDeclr
  replacePolyTypes (CNestedFunDef cFunDef) =
    CNestedFunDef <$> replacePolyTypes cFunDef

instance ReplacePolyTypes CDecl where
  replacePolyTypes (CDecl cDeclSpecs cDeclDecls a) = do
    cDeclSpecs' <- replacePolyTypes cDeclSpecs
    cDeclDecls' <- replacePolyTypes cDeclDecls
    return $ CDecl cDeclSpecs' cDeclDecls' a

instance ReplacePolyTypes CDeclDecl where
  replacePolyTypes (mDeclr, mInit, mExpr) = do
    mDeclr' <- replacePolyTypes mDeclr
    mInit' <- replacePolyTypes mInit
    mExpr' <- replacePolyTypes mExpr
    return (mDeclr', mInit', mExpr')

instance ReplacePolyTypes CInit where
  replacePolyTypes (CInitExpr cExpr a) =
    flip CInitExpr a <$> replacePolyTypes cExpr
  replacePolyTypes (CInitList cInitList a) =
    flip CInitList a <$> replacePolyTypes cInitList

instance ReplacePolyTypes CInitListItem where
  replacePolyTypes (cDesigs, cInit) = do
    cDesigs' <- replacePolyTypes cDesigs
    cInit' <- replacePolyTypes cInit
    return (cDesigs', cInit')

instance ReplacePolyTypes CDesignator where
  replacePolyTypes (CArrDesig cExpr a) =
    flip CArrDesig a <$> replacePolyTypes cExpr
  replacePolyTypes cMemberDesig@CMemberDesig{} =
    return cMemberDesig
  replacePolyTypes (CRangeDesig cExpr1 cExpr2 a) = do
    cExpr1' <- replacePolyTypes cExpr1
    cExpr2' <- replacePolyTypes cExpr2
    return $ CRangeDesig cExpr1' cExpr2' a

instance ReplacePolyTypes CDeclSpec where
  replacePolyTypes (CTypeSpec cTypeSpec) =
    CTypeSpec <$> replacePolyTypes cTypeSpec
  replacePolyTypes (CAlignSpec cAlignSpec) =
    CAlignSpec <$> replacePolyTypes cAlignSpec
  replacePolyTypes a = return a

instance ReplacePolyTypes CTypeSpec where
  replacePolyTypes cTypeDef@(CTypeDef ident@(Ident _ _ pos) a) = do
    let sId = getCName ident
    pTs <- gets polyTypes
    if sId `Map.member` pTs
      then do
        sId' <- polyAnonRename sId
        pMs <- gets polyMaps
        let pM : pMt = pMs
        modify
          (\state ->
            state{polyMaps = Map.insert sId' sId pM : pMt}
          )
        return $ CTypeDef (Ident (T.unpack sId') (quad (T.unpack sId')) pos) a
      else return cTypeDef
  replacePolyTypes (CTypeOfExpr cExpr a) =
    flip CTypeOfExpr a <$> replacePolyTypes cExpr
  replacePolyTypes (CTypeOfType cDeclr a) =
    flip CTypeOfType a <$> replacePolyTypes cDeclr
  replacePolyTypes (CAtomicType cDeclr a) =
    flip CAtomicType a <$> replacePolyTypes cDeclr
  replacePolyTypes a = return a

instance ReplacePolyTypes CAlignSpec where
  replacePolyTypes (CAlignAsType cDeclr a) =
    flip CAlignAsType a <$> replacePolyTypes cDeclr
  replacePolyTypes (CAlignAsExpr cExpr a) =
    flip CAlignAsExpr a <$> replacePolyTypes cExpr

instance ReplacePolyTypes CDeclr where
  replacePolyTypes (CDeclr mIdent cDerivedDeclrs mStrLit cAttrs a) = do
    cDerivedDeclrs' <- replacePolyTypes cDerivedDeclrs
    cAttrs' <- replacePolyTypes cAttrs
    return $ CDeclr mIdent cDerivedDeclrs' mStrLit cAttrs' a
  replacePolyTypes (CHMDeclr cDeclr chmPars a) = do
    cDeclr' <- replacePolyTypes cDeclr
    chmPars' <- replacePolyTypes chmPars
    return $ CHMDeclr cDeclr' chmPars' a

instance ReplacePolyTypes CAttr where
  replacePolyTypes (CAttr ident cExprs a) =
    flip (CAttr ident) a <$> replacePolyTypes cExprs

instance ReplacePolyTypes CDerivedDeclr where
  replacePolyTypes (CFunDeclr (Left idents) cAttrs a) =
    flip (CFunDeclr (Left idents)) a <$> replacePolyTypes cAttrs
  replacePolyTypes (CFunDeclr (Right (cDeclrs, varArgs)) cAttrs a) = do
    cDeclrs' <- replacePolyTypes cDeclrs
    cAttrs' <- replacePolyTypes cAttrs
    return $ CFunDeclr (Right (cDeclrs', varArgs)) cAttrs' a
  -- CPtrDeclr, CArrDeclr
  replacePolyTypes a = return a

instance ReplacePolyTypes CHMParams where
  replacePolyTypes (CHMParams chmTypes a) =
    flip CHMParams a <$> replacePolyTypes chmTypes

instance ReplacePolyTypes CHMT where
  replacePolyTypes (CHMCType cDeclSpecs a) =
    flip CHMCType a <$> replacePolyTypes cDeclSpecs
  replacePolyTypes (CHMParType chmType chmPars a) = do
    chmType' <- replacePolyTypes chmType
    chmPars' <- replacePolyTypes chmPars
    return $ CHMParType chmType' chmPars' a

instance ReplacePolyTypes CExpr where
  replacePolyTypes (CComma cExprs a) =
    flip CComma a <$> replacePolyTypes cExprs
  replacePolyTypes (CAssign assOp lExpr rExpr a) = do
    lExpr' <- replacePolyTypes lExpr
    rExpr' <- replacePolyTypes rExpr
    return $ CAssign assOp lExpr' rExpr' a
  replacePolyTypes (CCond cExpr (Just cThen) cElse a) = do
    cExpr' <- replacePolyTypes cExpr
    cThen' <- replacePolyTypes cThen
    cElse' <- replacePolyTypes cElse
    return $ CCond cExpr' (Just cThen') cElse' a
  replacePolyTypes (CBinary binOp cLeft cRight a) = do
    cLeft' <- replacePolyTypes cLeft
    cRight' <- replacePolyTypes cRight
    return $ CBinary binOp cLeft' cRight' a
  replacePolyTypes (CCast cDecl cExpr a) = do
    cDecl' <- replacePolyTypes cDecl
    cExpr' <- replacePolyTypes cExpr
    return $ CCast cDecl' cExpr' a
  replacePolyTypes (CUnary unOp cExpr a) =
    flip (CUnary unOp) a <$> replacePolyTypes cExpr
  replacePolyTypes (CSizeofExpr cExpr a) =
    flip CSizeofExpr a <$> replacePolyTypes cExpr
  replacePolyTypes (CSizeofType cExpr a) =
    flip CSizeofType a <$> replacePolyTypes cExpr
  replacePolyTypes (CAlignofExpr cExpr a) =
    flip CAlignofExpr a <$> replacePolyTypes cExpr
  replacePolyTypes (CAlignofType cExpr a) =
    flip CAlignofType a <$> replacePolyTypes cExpr
  replacePolyTypes (CComplexReal cExpr a) =
    flip CComplexReal a <$> replacePolyTypes cExpr
  replacePolyTypes (CComplexImag cExpr a) =
    flip CComplexImag a <$> replacePolyTypes cExpr
  replacePolyTypes (CIndex aExpr iExpr a) = do
    aExpr' <- replacePolyTypes aExpr
    iExpr' <- replacePolyTypes iExpr
    return $ CIndex aExpr' iExpr' a
  replacePolyTypes (CCall cExpr cExprs a) = do
    cExpr' <- replacePolyTypes cExpr
    cExprs' <- replacePolyTypes cExprs
    return $ CCall cExpr' cExprs' a
  replacePolyTypes (CMember cExpr ident deref a) = do
    cExpr' <- replacePolyTypes cExpr
    return $ CMember cExpr' ident deref a
  replacePolyTypes cVar@(CVar ident@(Ident _ _ pos) a) = do
    let vId = getCName ident
    pTs <- gets polyTypes
    if vId `Map.member` pTs
      then do
        vId' <- polyAnonRename vId
        pMs <- gets polyMaps
        let pM : pMt = pMs
        modify (\state -> state{polyMaps = Map.insert vId' vId pM : pMt})
        return $ CVar (makeIdent vId' pos) a
      else return cVar
  replacePolyTypes cConst@(CConst _) =
    return cConst
  replacePolyTypes (CCompoundLit cDecl cInitList a) = do
    cDecl' <- replacePolyTypes cDecl
    cInitList' <- replacePolyTypes cInitList
    return $ CCompoundLit cDecl' cInitList' a
  -- TODO: CGenericSelection
  replacePolyTypes (CStatExpr cStat a) =
    flip CStatExpr a <$> replacePolyTypes cStat
  replacePolyTypes cLabAddrExpr@(CLabAddrExpr _ _) =
    return cLabAddrExpr
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
  replacePolyTypes as = traverse replacePolyTypes as

instance ReplacePolyTypes a => ReplacePolyTypes (Maybe a) where
  replacePolyTypes Nothing = return Nothing
  replacePolyTypes (Just a) = Just <$> replacePolyTypes a

instance
  (ReplacePolyTypes a, ReplacePolyTypes b) =>
    ReplacePolyTypes (Either a b) where
  replacePolyTypes e = traverse replacePolyTypes e

instantiate :: CExtDecl -> Scheme -> IState ()
instantiate extFunDef scheme = do
  when (typeComplexity scheme > 500) . error $
    niceError
      "Type too complex, detected possible instantiation of an infinite type"
      (nodeInfo extFunDef)
  syncScopes
  pushPolyMaps
  extFunDef' <- replacePolyTypes extFunDef
  polyMap <- gets (head . polyMaps)
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
  modify (\state -> state{transformState = tState})
  sequence_
    [ case name' `Map.lookup` polyMap of
        (Just name) -> do
          pTs <- gets polyTypes
          let
            pType = pTs Map.! name
            mangledName = T.concat [dUnderScore, name, mangle scheme']
          if mangledName `Set.member` pTypeInstances pType
            then return ()
            else addPolyTypeInstance name mangledName >> instantiate (pTypeDefinition pType) scheme'
        Nothing -> return ()
    | (name', scheme') <- Map.toList as
    ]
  let
    funName = getCName extFunDef'
    tVarMap =
      (\name' -> if let (f, s) = T.span (/= ':') name' in f == funName && s /= mempty
          then T.drop (T.length funName + 1) name'
          else name'
      ) `Map.mapKeys` as
    -- TODO: i cannot remember what
  extFunDef'' <- replaceTVars tVarMap extFunDef' >>= flip rewrite scheme
  pullPolyMaps
  enqueueExtDecl extFunDef''

class ReplaceTVars a where
  replaceTVars :: Map.Map Id Scheme -> a -> IState a

instance ReplaceTVars CExtDecl where
  replaceTVars as (CHMFDefExt chmFunDef) =
    CHMFDefExt <$> replaceTVars as chmFunDef
  replaceTVars as (CFDefExt cFunDef) =
    CFDefExt <$> replaceTVars as cFunDef
  replaceTVars as (CDeclExt cDecl) =
    CDeclExt <$> replaceTVars as cDecl
  replaceTVars as (CHMSDefExt chmStructDef) =
    CHMSDefExt <$> replaceTVars as chmStructDef

instance ReplaceTVars CHMStructDef where
  replaceTVars as (CHMStructDef chmHead cStructUnion a) =
    flip (CHMStructDef chmHead) a <$> replaceTVars as cStructUnion

instance ReplaceTVars CStructUnion where
  replaceTVars as (CStruct cStructTag mIdent mDecls cAttrs a) = do
    mDecls' <- replaceTVars as mDecls
    cAttrs' <- replaceTVars as cAttrs
    return $ CStruct cStructTag mIdent mDecls' cAttrs' a

instance ReplaceTVars CHMFunDef where
  replaceTVars as (CHMFunDef chmHead cFunDef a) =
    flip (CHMFunDef chmHead) a <$> replaceTVars as cFunDef

instance ReplaceTVars CFunDef where
  replaceTVars as (CFunDef specs cDeclr decls stmt a) = do
    specs' <- replaceTVars as specs
    cDeclr' <- replaceTVars as cDeclr
    decls' <- replaceTVars as decls
    stmt' <- replaceTVars as stmt
    return $ CFunDef specs' cDeclr' decls' stmt' a

instance ReplaceTVars CDeclSpec where
  replaceTVars as (CTypeSpec cTypeSpec) =
    CTypeSpec <$> replaceTVars as cTypeSpec
  replaceTVars as (CAlignSpec cAlignSpec) =
    CAlignSpec <$> replaceTVars as cAlignSpec
  replaceTVars as anon@(CHMAnonType nInfo) = do
    mScheme <- (as Map.!?) <$> runTState (mangleAnonType anon)
    monoType <- case trace (show as) mScheme of
      Just scheme -> schemeToMono scheme nInfo
      _ -> return $ T.pack "not yet supported"
    return . CTypeSpec $ CTypeDef (makeIdent monoType nInfo) nInfo
  replaceTVars _ a = return a

class IsDetType a where
  isDetType :: a -> Bool

instance IsDetType Type where
  isDetType (TVar _) = False
  isDetType (TCon _) = True
  isDetType (TAp a b) =
    isDetType a && isDetType b
  isDetType (TGen _) = False

instance IsDetType Scheme where
  isDetType (Forall tVs (_ :=> t)) =
    null tVs && isDetType t

typeToMono :: Type -> NodeInfo -> IState Id
typeToMono t@(TCon (Tycon tId _)) _ =
  case tId `Map.lookup` builtinTypes of
    Just name -> return name
    _ -> return tId
typeToMono t nInfo = do
  sIs <- gets schemeInstances
  let t' = mangleType t
  unless
    (t' `Set.member` sIs)
    (instantiateType t' t nInfo)
  return t'

makeIdent :: Id -> NodeInfo -> Ident
makeIdent name nInfo =
  Ident (T.unpack name) (quad (T.unpack name)) nInfo

createEmptyDeclr :: Id -> NodeInfo -> CDeclr
createEmptyDeclr name nInfo =
  CDeclr (Just $ makeIdent name nInfo) [] Nothing [] nInfo

addDerivedDeclr :: CDerivedDeclr -> CDeclr -> CDeclr
addDerivedDeclr cDerivedDeclr (CDeclr a cDerivedDeclrs c d e) =
  CDeclr a (cDerivedDeclr : cDerivedDeclrs) c d e

typedefSpec :: Id -> NodeInfo -> CDeclSpec
typedefSpec name nInfo =
  CTypeSpec (CTypeDef (makeIdent name nInfo) nInfo)

typeDecl :: Id -> NodeInfo -> CDecl
typeDecl name nInfo =
  CDecl [typedefSpec name nInfo] [] nInfo

instantiateType, instantiateTypeInner :: Id -> Type -> NodeInfo -> IState ()
instantiateType name t nInfo = do
  modify (\state -> state{schemeInstances = name `Set.insert` schemeInstances state})
  instantiateTypeInner name t nInfo

instantiateTypeInner name t@(TAp (TAp (TCon (Tycon tArr _)) t1) t2) nInfo
  | tArr == tArrowId = do
    let
      getParams (TAp tA tB) = do
        tA' <- getParams tA
        tB' <- typeToMono tB nInfo
        return $ tB' : tA'
      getParams _ = return []
    t1' <- reverse <$> getParams t1  -- at least I hope it should be reversed
    t2' <- typeToMono t2 nInfo
    let
      cDecl = CDeclExt $ CDecl
        [CStorageSpec (CTypedef nInfo), typedefSpec t2' nInfo]
        [ ( Just . addDerivedDeclr (CFunDeclr (Right (flip typeDecl nInfo <$> t1', False)) [] nInfo) $ createEmptyDeclr name nInfo
          , Nothing
          , Nothing)
        ]
        nInfo
    enqueueExtDecl cDecl
  | otherwise = instantiateTypeInnerHelper name t nInfo
instantiateTypeInner name t@(TAp t1 t2) nInfo =
  instantiateTypeInnerHelper name t nInfo
instantiateTypeInnerHelper name t@(TAp t1 t2) nInfo =
  if t1 == tPointer then do
    t2' <- typeToMono t2 nInfo
    let
      cDecl = CDeclExt $ CDecl
        [CStorageSpec (CTypedef nInfo), typedefSpec t2' nInfo]
        [ ( Just . addDerivedDeclr (CPtrDeclr [] nInfo) $ createEmptyDeclr name nInfo
          , Nothing
          , Nothing)
        ]
        nInfo
    enqueueExtDecl cDecl
  else do
    state <- get
    let
      getLeftest (TAp tA tB) = getLeftest tA
      getLeftest tA = tA
      (TCon (Tycon t' _)) = getLeftest t
    case t' `Map.lookup` polyStructUnions state of
      Just pType ->
        instantiate (pTypeDefinition pType) (toScheme t)

schemeToMono :: Scheme -> NodeInfo -> IState Id
schemeToMono scheme@(Forall tVs (cs :=> t)) nInfo = do
  unless (isDetType scheme) . error $
    niceError
      "Cannot determine monotype"
      nInfo
  typeToMono t nInfo


instance ReplaceTVars CTypeSpec where
  replaceTVars as cTypeDef@(CTypeDef ident@(Ident _ a b) c) =
    case getCName ident `Map.lookup` as of
      (Just scheme) -> do
        monoType <- schemeToMono scheme b
        return $ CTypeDef (makeIdent monoType b) c
      Nothing -> return cTypeDef
  replaceTVars as (CTypeOfExpr cExpr a) =
    flip CTypeOfExpr a <$> replaceTVars as cExpr
  replaceTVars as (CTypeOfType cDeclr a) =
    flip CTypeOfType a <$> replaceTVars as cDeclr
  replaceTVars as (CAtomicType cDeclr a) =
    flip CAtomicType a <$> replaceTVars as cDeclr
  replaceTVars _ a = return a

instance ReplaceTVars CAlignSpec where
  replaceTVars as (CAlignAsType cDeclr a) =
    flip CAlignAsType a <$> replaceTVars as cDeclr
  replaceTVars as (CAlignAsExpr cExpr a) =
    flip CAlignAsExpr a <$> replaceTVars as cExpr

instance ReplaceTVars CDeclr where
  replaceTVars as (CDeclr mIdent cDerivedDeclrs mStrLit cAttrs a) = do
    cDerivedDeclrs' <- replaceTVars as cDerivedDeclrs
    cAttrs' <- replaceTVars as cAttrs
    return $ CDeclr mIdent cDerivedDeclrs' mStrLit cAttrs' a
  replaceTVars as (CHMDeclr cDeclr chmPars a) = do
    cDeclr' <- replaceTVars as cDeclr
    chmPars' <- replaceTVars as chmPars
    return $ CHMDeclr cDeclr chmPars a

instance ReplaceTVars CDerivedDeclr where
  replaceTVars as (CFunDeclr (Left idents) cAttrs a) =
    flip (CFunDeclr (Left idents)) a <$> replaceTVars as cAttrs
  replaceTVars as (CFunDeclr (Right (cDeclrs, varArgs)) cAttrs a) = do
    cDeclrs' <- replaceTVars as cDeclrs
    cAttrs' <- replaceTVars as cAttrs
    return $ CFunDeclr (Right (cDeclrs', varArgs)) cAttrs' a
  -- CPtrDeclr and CArrDeclr
  replaceTVars _ a = return a

instance ReplaceTVars CHMParams where
  replaceTVars as (CHMParams chmTypes a) =
    flip CHMParams a <$> replaceTVars as chmTypes

instance ReplaceTVars CHMT where
  replaceTVars as (CHMCType cDeclSpecs a) =
    flip CHMCType a <$> replaceTVars as cDeclSpecs
  replaceTVars as (CHMParType chmType chmPars a) = do
    chmType' <- replaceTVars as chmType
    chmPars' <- replaceTVars as chmPars
    return $ CHMParType chmType' chmPars' a

type CDeclDecl = (Maybe CDeclr, Maybe CInit, Maybe CExpr)

instance ReplaceTVars CDecl where
  replaceTVars as (CDecl cDeclSpecs cDeclDecls a) = do
    cDeclSpecs' <- replaceTVars as cDeclSpecs
    cDeclDecls' <- replaceTVars as cDeclDecls
    return $ CDecl cDeclSpecs' cDeclDecls' a

instance ReplaceTVars CDeclDecl where
  replaceTVars as (mDeclr, mInit, mExpr) = do
    mDeclr' <- replaceTVars as mDeclr
    mInit' <- replaceTVars as mInit
    mExpr' <- replaceTVars as mExpr
    return (mDeclr', mInit', mExpr')

instance ReplaceTVars CInit where
  replaceTVars as (CInitExpr cExpr a) =
    flip CInitExpr a <$> replaceTVars as cExpr
  replaceTVars as (CInitList cInitList a) =
    flip CInitList a <$> replaceTVars as cInitList

type CInitListItem = ([CDesignator], CInit)

instance ReplaceTVars CInitListItem where
  replaceTVars as (cDesignators, cInit) = do
    cDesignators' <- replaceTVars as cDesignators
    cInit' <- replaceTVars as cInit
    return (cDesignators', cInit')

instance ReplaceTVars CDesignator where
  replaceTVars as (CArrDesig cExpr a) =
    flip CArrDesig a <$> replaceTVars as cExpr
  replaceTVars as cMemberDesig@CMemberDesig{} = return cMemberDesig
  replaceTVars as (CRangeDesig cExpr1 cExpr2 a) = do
    cExpr1' <- replaceTVars as cExpr1
    cExpr2' <- replaceTVars as cExpr2
    return $ CRangeDesig cExpr1 cExpr2 a

instance ReplaceTVars CStat where
  replaceTVars as (CLabel ident cStmt cAttrs a) = do
    cStmt' <- replaceTVars as cStmt
    cAttrs' <- replaceTVars as cAttrs
    return $ CLabel ident cStmt' cAttrs' a
  replaceTVars as (CCase cExpr cStmt a) = do
    cExpr' <- replaceTVars as cExpr
    cStmt' <- replaceTVars as cStmt
    return $ CCase cExpr' cStmt' a
  replaceTVars as (CCases cExpr1 cExpr2 cStmt a) = do
    cExpr1' <- replaceTVars as cExpr1
    cExpr2' <- replaceTVars as cExpr2
    cStmt' <- replaceTVars as cStmt
    return $ CCases cExpr1' cExpr2' cStmt' a
  replaceTVars as (CDefault cStmt a) =
    flip CDefault a <$> replaceTVars as cStmt
  replaceTVars as (CExpr mExpr a) =
    flip CExpr a <$> replaceTVars as mExpr
  replaceTVars as (CCompound idents cBlockItems a) =
    flip (CCompound idents) a <$> replaceTVars as cBlockItems
  replaceTVars as (CIf cExpr cStmt mStmt a) = do
    cExpr' <- replaceTVars as cExpr
    cStmt' <- replaceTVars as cStmt
    mStmt' <- replaceTVars as mStmt
    return $ CIf cExpr' cStmt' mStmt' a
  replaceTVars as (CFor eExprDecl mExpr2 mExpr3 cStat a) = do
    eExprDecl' <- replaceTVars as eExprDecl
    mExpr2' <- replaceTVars as mExpr2
    mExpr3' <- replaceTVars as mExpr3
    cStat' <- replaceTVars as cStat
    return $ CFor eExprDecl' mExpr2' mExpr3' cStat' a
  replaceTVars as cGoto@CGoto{} = return cGoto
  replaceTVars as (CGotoPtr cExpr a) =
    flip CGotoPtr a <$> replaceTVars as cExpr
  replaceTVars as cCont@CCont{} = return cCont
  replaceTVars as cBreak@CBreak{} = return cBreak
  replaceTVars as (CReturn mExpr a) =
    flip CReturn a <$> replaceTVars as mExpr
  replaceTVars as cAsm@CAsm{} = return cAsm

instance ReplaceTVars CBlockItem where
  replaceTVars as (CBlockStmt cStmt) =
    CBlockStmt <$> replaceTVars as cStmt
  replaceTVars as (CBlockDecl cDeclr) =
    CBlockDecl <$> replaceTVars as cDeclr
  replaceTVars as (CNestedFunDef cFunDef) =
    CNestedFunDef <$> replaceTVars as cFunDef

instance ReplaceTVars CAttr where
  replaceTVars as (CAttr ident cExprs a) =
    flip (CAttr ident) a <$> replaceTVars as cExprs

instance ReplaceTVars CExpr where
  replaceTVars as (CComma cExprs a) =
    flip CComma a <$> replaceTVars as cExprs
  replaceTVars as (CAssign assOp cExpr1 cExpr2 a) = do
    cExpr1' <- replaceTVars as cExpr1
    cExpr2' <- replaceTVars as cExpr2
    return $ CAssign assOp cExpr1' cExpr2' a
  replaceTVars as (CCond cExpr1 mExpr cExpr2 a) = do
    cExpr1' <- replaceTVars as cExpr1
    mExpr' <- replaceTVars as mExpr
    cExpr2' <- replaceTVars as cExpr2
    return $ CCond cExpr1' mExpr' cExpr2' a
  replaceTVars as (CBinary binOp cExpr1 cExpr2 a) = do
    cExpr1' <- replaceTVars as cExpr1
    cExpr2' <- replaceTVars as cExpr2
    return $ CBinary binOp cExpr1' cExpr2' a
  replaceTVars as (CCast cDeclr cExpr a) = do
    cDeclr' <- replaceTVars as cDeclr
    cExpr' <- replaceTVars as cExpr
    return $ CCast cDeclr' cExpr' a
  replaceTVars as (CUnary unOp cExpr a) =
    flip (CUnary unOp) a <$> replaceTVars as cExpr
  replaceTVars as (CSizeofExpr cExpr a) =
    flip CSizeofExpr a <$> replaceTVars as cExpr
  replaceTVars as (CSizeofType cDeclr a) =
    flip CSizeofType a <$> replaceTVars as cDeclr
  replaceTVars as (CAlignofExpr cExpr a) =
    flip CAlignofExpr a <$> replaceTVars as cExpr
  replaceTVars as (CAlignofType cDeclr a) =
    flip CAlignofType a <$> replaceTVars as cDeclr
  replaceTVars as (CComplexReal cExpr a) =
    flip CComplexReal a <$> replaceTVars as cExpr
  replaceTVars as (CComplexImag cExpr a) =
    flip CComplexImag a <$> replaceTVars as cExpr
  replaceTVars as (CIndex cExpr1 cExpr2 a) = do
    cExpr1' <- replaceTVars as cExpr1
    cExpr2' <- replaceTVars as cExpr2
    return $ CIndex cExpr1' cExpr2' a
  replaceTVars as (CCall cExpr cExprs a) = do
    cExpr' <- replaceTVars as cExpr
    cExprs' <- replaceTVars as cExprs
    return $ CCall cExpr' cExprs' a
  replaceTVars as (CMember cExpr ident deref a) =
    flip (flip (`CMember` ident) deref) a <$> replaceTVars as cExpr
  replaceTVars as cVar@(CVar ident@(Ident _ _ pos) a) =
    let sId = getCName ident
    in case sId `Map.lookup` as of
      Just scheme -> do
        polyMap <- gets (head . polyMaps)
        let name = T.concat [dUnderScore, polyMap Map.! sId, mangle scheme]
        return $ CVar (makeIdent name pos) a
      Nothing -> return cVar
  replaceTVars as cConst@CConst{} = return cConst
  replaceTVars as (CCompoundLit cDeclr cInitList a) = do
    cDeclr' <- replaceTVars as cDeclr
    cInitList' <- replaceTVars as cInitList
    return $ CCompoundLit cDeclr' cInitList' a
  replaceTVars as CGenericSelection{} =
    error "not supporting c generic selections"
  replaceTVars as (CStatExpr cStmt a) =
    flip CStatExpr a <$> replaceTVars as cStmt
  replaceTVars as cLabAddrExpr@CLabAddrExpr{} = return cLabAddrExpr
  replaceTVars as CBuiltinExpr{} =
    error "not supporting builtinThing"

instance ReplaceTVars b => ReplaceTVars [b] where
  replaceTVars as bs = traverse (replaceTVars as) bs

instance ReplaceTVars b => ReplaceTVars (Maybe b) where
  replaceTVars as m = traverse (replaceTVars as) m

instance (ReplaceTVars a, ReplaceTVars b) => ReplaceTVars (Either a b) where
  replaceTVars as e = traverse (replaceTVars as) e

class RenameCDef a where
  renameCDef :: Id -> a -> a

instance RenameCDef CFunDef where
  renameCDef name (CFunDef cDeclSpecs cDeclr cDecls cStmt a) =
    CFunDef cDeclSpecs (renameCDef name cDeclr) cDecls cStmt a

instance RenameCDef CStructUnion where
  renameCDef name (CStruct cStructTag (Just cIdent) mDecls cAttrs a) =
    CStruct cStructTag (Just . renameCDef name $ cIdent) mDecls cAttrs a

instance RenameCDef CDeclr where
  renameCDef name (CDeclr (Just cIdent) cDerivedDeclrs mStrLit cAttrs a) =
    CDeclr (Just . renameCDef name $ cIdent) cDerivedDeclrs mStrLit cAttrs a

instance RenameCDef Ident where
  renameCDef name (Ident sId _ pos) =
    makeIdent name pos

class GetFunDef a where
  getFunDef :: a -> CFunDef

instance GetFunDef CExtDecl where
  getFunDef (CFDefExt cFunDef) = cFunDef
  getFunDef (CHMFDefExt chmFunDef) = getFunDef chmFunDef

instance GetFunDef CHMFunDef where
  getFunDef (CHMFunDef _ cFunDef _) = cFunDef

instantiateSUType :: CStructUnion -> Scheme -> IState ()
instantiateSUType (CStruct cStructTag (Just name) _ _ nInfo) scheme = do
  let
    scheme' = mangle scheme
    name' = T.tail scheme'
  enqueueExtDecl
      ( CDeclExt $
         CDecl
            [ CStorageSpec (CTypedef nInfo)
            , CTypeSpec $ CSUType
                ( CStruct
                    cStructTag
                    (Just $ makeIdent name' nInfo)
                    Nothing
                    []
                    nInfo)
                nInfo
            ]
            [ ( Just $ createEmptyDeclr name' nInfo
              , Nothing
              , Nothing
            ) ]
            nInfo
      )

rewrite :: CExtDecl -> Scheme -> IState CExtDecl
rewrite cExtDecl@CFDefExt{} _ = return cExtDecl
rewrite cExtDecl@(CHMSDefExt (CHMStructDef _ cStructUnion _)) scheme = do
  let
    name = getCName cStructUnion
    scheme' = T.tail $ mangle scheme
    cStructUnion' = renameCDef scheme' cStructUnion
    nInfo = nodeInfo cStructUnion'
  instantiateSUType cStructUnion scheme
  return . CDeclExt $ CDecl
      [CTypeSpec $ CSUType cStructUnion' nInfo]
      []
      nInfo
rewrite cExtDecl@(CHMFDefExt (CHMFunDef chmHead cFunDef _)) scheme =
  let name = getCName cFunDef
  in return . CFDefExt $ renameCDef (T.concat [dUnderScore, name, mangle scheme]) cFunDef
rewrite cExtDecl scheme@(Forall [] (cs :=> t)) = do
  let name = getCName cExtDecl
  pType <- gets ((Map.! name) . polyTypes)
  let
    Just cId = pTypeClass pType
    Just (IsIn _ cT) = List.find (\(IsIn cId' t') -> cId' == cId) cs
    substs = catMaybes  -- TODO
      [ if c == cT
           --- || not (null . runTI $ mgu cT c)
          then Just def
          else Nothing
      | (c, def) <- Map.toList (pTypeDefinitions pType)
      ]
  case substs of
    [] -> error "cannot create the instance"
    [iDef] -> return . CFDefExt $ renameCDef (T.concat [dUnderScore, name, mangle scheme]) (getFunDef iDef)
    _ -> error "I don't know yet"  -- TODO

parseReSchemedVirtual :: Scheme -> CExtDecl -> BindGroup -> IState (Map.Map Id Scheme)
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
            , ( parExpls <> [ (T.concat [dUnderScore, name, mangle scheme]
                  , scheme
                  , alts
                  )
                ]
              , []
              )
            ]
        CDeclExt{} -> transform cExtDecl >>= typeInfer pAs . (bindGroup:)
        CHMSDefExt (CHMStructDef chmHead@(CHMHead tVars chmConstrs _) cStructUnion _) -> do
          let
            name = getCName cExtDecl
            sKind = takeNKind $ length tVars
            tVarNames =
              [ name <> (':' `T.cons` getCName tVar)
              | tVar <- tVars
              ]
            enScopeType set (TAp t1 t2) =
              enScopeType set t1 `TAp` enScopeType set t2
            enScopeType set t@(TVar (Tyvar id kind)) =
              if id `Set.member` set
                then TVar (Tyvar (name <> (':' `T.cons` id)) kind)
                else t
            enScopeType _ t = t
            tVars' =
              TVar . flip Tyvar Star <$> tVarNames -- TODO: doesn't have to be just Star
            sType =
              foldl TAp (TCon (Tycon name sKind)) tVars'
            parExpls = zip3 tVarNames (toScheme <$> tVars') (repeat [])
          enterCHMHead
          _ <- transform chmHead
          aliases <-
            ((\(i :>: Forall [] ([] :=> t)) ->
              (name <> (':' `T.cons` i), toScheme $ enScopeType (Set.fromList $ getCName <$> tVars) t, [])) <$>) <$> getAliases chmConstrs
          let
          leaveCHMHead
          typeInfer pAs
            [ bindGroup
            , ( parExpls <> aliases <> [ ( mangle scheme
                  , scheme
                  , [([], Const (name :>: toScheme sType))]
                  )
                ]
              , []
              )
            ]
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

parse :: Transform a => a -> IState (Map.Map Id Scheme)
parse a = do
  state@InstantiateMonad{transformState = tS, parsedAssumps = pAs} <- get
  let (as, tS') = runState (transform a >>= typeInfer pAs) tS
  put state
    { transformState = tS'
    , parsedAssumps = as <> pAs
    }
  return as

parse_ :: Transform a => a -> IState ()
parse_ = (>> return ()) . parse

mangleScheme :: Scheme -> Id
mangleScheme (Forall [] (cs :=> t)) = mangleType t

builtinTypes :: Map.Map Id Id
builtinTypes = Map.fromList
  [ (tCharId, T.pack "char")
  , (tIntId, T.pack "int")
  , (tFloatId, T.pack "float")
  , (tDoubleId, T.pack "double")
  ]

packTC = T.pack "TC"
packTF = T.pack "TF"
packTP = T.pack "TP"
packTA = T.pack "TA"

mangleType :: Type -> Id
mangleType (TCon (Tycon id _)) = case id `Map.lookup` builtinTypes of
  Nothing -> T.concat [packTC, T.pack $ show (T.length id), id]
  Just cName -> cName
mangleType t@(TAp (TAp (TCon (Tycon tArr _)) t1) t2)
  | tArr == tArrowId = let
      t1' = manglePars t1
      t2' = mangleType t2
    in T.concat [packTF, T.pack $ show (T.length t1'), t1', T.pack $ show (T.length t2'), t2']
  | otherwise = mangleTypeHelper t

mangleType (TAp t1 t2) =
  mangleTypeHelper (TAp t1 t2)
mangleTypeHelper (TAp t1 t2)
  | t1 == tPointer = let
      t1' = mangleType t2
    in T.concat [packTP, T.pack $ show (T.length t1'), t1']
  | otherwise = let
      t1' = mangleType t1
      t2' = mangleType t2
    in T.concat [packTA, T.pack $ show (T.length t1'), t1', T.pack $ show (T.length t2'), t2']

manglePars :: Type -> Id
manglePars TCon{} = mempty
manglePars (TAp t1 t2) =
  let
    t1' = manglePars t1
    t2' = mangleType t2
  in t1' <> t2'

class Mangle a where
  mangle :: a -> Id

instance Mangle Type where
  mangle t = '_' `T.cons` mangleType t

instance Mangle Scheme where
  mangle s = '_' `T.cons` mangleScheme s
