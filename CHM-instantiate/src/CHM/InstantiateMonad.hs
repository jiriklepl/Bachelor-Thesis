{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module CHM.InstantiateMonad where

import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.Set as Set
import Data.Char

import Language.C.Syntax
import Language.C.Data
import Language.C.Data.Ident (Ident(..))

import TypingHaskellInHaskell
import CHM.Transform

type IState = State InstantiateMonad

data PolyType = PolyType
  { definition :: CExtDecl
  , instances  :: Set.Set Id
  }

data InstantiateMonad = InstantiateMonad
  { parsedAssumps  :: [Assump]
  , transformState :: TransformMonad
  , lastScopeCopy  :: Int
  , polyTypes      :: Map.Map Id PolyType
  , polyAnonNumber :: Int
  }

initInstantiateMonad :: InstantiateMonad
initInstantiateMonad = InstantiateMonad
  { parsedAssumps  = []
  , transformState = initTransformMonad
  , lastScopeCopy  = 0
  , polyTypes      = Map.empty
  , polyAnonNumber = 0
  }

polyAnonRename :: Id -> IState Id
polyAnonRename id = do
  state@InstantiateMonad{polyAnonNumber = pAN} <- get
  put state{polyAnonNumber = pAN + 1}
  return $ id ++ show pAN

addPolyTypeInstance :: Id -> Id -> IState ()
addPolyTypeInstance pId iId = do
  state@InstantiateMonad{polyTypes = pTs} <- get
  put state
    { polyTypes = Map.adjust (\pType -> pType{instances = iId `Set.insert` instances pType}) pId pTs
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

instance  ReplacePolyTypes CBlockItem where  -- TODO:
  replacePolyTypes (CBlockStmt cStat) = do
    (cStat', statMap) <- replacePolyTypes cStat
    return (CBlockStmt cStat', statMap)

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
    InstantiateMonad{polyTypes = pTs} <- get
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
    replaceAs <- traverse replacePolyTypes as
    return (fst <$> replaceAs, foldl Map.union Map.empty (snd <$> replaceAs))

instantiate :: CExtDecl -> Scheme -> IState [CExtDecl]
instantiate extFunDef scheme = do
  syncScopes
  (extFunDef', polyMap) <- replacePolyTypes extFunDef
  let
    expls =
      [ ( var
        , toScheme $ TVar $ Tyvar ("@TV:"++var) Star
        , [([],Var real)]
        )
      | (var, real) <- Map.toList polyMap
      ]
  as <- parseReSchemedVirtual scheme extFunDef' (expls, [])
  InstantiateMonad{polyTypes = pTs} <- get
  children <- concat <$> sequence
    [ case name' `Map.lookup` polyMap of
        (Just name) -> case name `Map.lookup` pTs of
          (Just pType) -> do
            let mangledName = name ++ mangleScheme scheme'
            if mangledName `Set.member` instances pType
              then addPolyTypeInstance name mangledName >> instantiate (definition pType) scheme'
              else return []
          Nothing ->
            return $ error "this is weird, like really this should not happen.."
        Nothing -> return []
    | (name' :>: scheme') <- as
    ]
  return $ reverse (extFunDef' : children)

parseReSchemedVirtual :: Scheme -> CExtDecl -> BindGroup -> IState [Assump]
parseReSchemedVirtual scheme cExtDecl bindGroup = do
  InstantiateMonad{transformState = tS, parsedAssumps = pAs} <- get
  let
    (as, tS') = flip runState tS $
      case cExtDecl of
        CFDefExt{} -> transform cExtDecl >>= typeInfer pAs . (bindGroup:)
        CHMFDefExt{} -> do
          cExtDecl' <- transformCHMFunDef cExtDecl
          let [([(name, polyScheme, alts)],[])] = cExtDecl'
          typeInfer pAs
            ( bindGroup
            : [ ( [ ( name ++ mangleScheme scheme
                    , polyScheme
                    , alts
                    )
                  ]
                , []
                )
              ]
            )
  return as


syncScopes :: IState ()
syncScopes = do
  state@InstantiateMonad{transformState = tS} <- get
  put state {lastScopeCopy = lastScope tS}

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
mangleScheme (Forall [] ([] :=> t)) = mangleType t

mangleType :: Type -> Id
{-
  mangleType (TAp (TAp tArrow t1) t2) =
    let
      t1' = mangleType t1
      t2' = mangleType t2
    in "fn_" ++ show (length t1') ++ t1' ++ show (length t2') ++ t2'
-}
mangleType (TCon (Tycon id _)) = "TC" ++ show (length id) ++ id
mangleType (TAp t1 t2) =
  let
    t1' = mangleType t1
    t2' = mangleType t2
  in show (length t1') ++ t1' ++ show (length t2') ++ t2'
