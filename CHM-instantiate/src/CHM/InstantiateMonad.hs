{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module CHM.InstantiateMonad where

import Control.Monad.State
import qualified Data.Map as Map
import qualified Data.Set as Set

import Language.C.Syntax
import Language.C.Data

import TypingHaskellInHaskell
import CHM.Transform

type IState = State InstantiateMonad

data PolyType = PolyType
  { definition :: CExtDecl
  , instances  :: (Set.Set Id)
  }

data InstantiateMonad = InstantiateMonad
  { parsedAssumps  :: [Assump]
  , transformState :: TransformMonad
  , lastScopeCopy  :: Int
  , polyTypes      :: Map.Map Id PolyType
  }

initInstantiateMonad :: InstantiateMonad
initInstantiateMonad = InstantiateMonad
  { parsedAssumps  = []
  , transformState = initTransformMonad
  , lastScopeCopy  = 0
  , polyTypes      = Map.empty
  }

addPolyTypeInstance :: Id -> Id -> IState ()
addPolyTypeInstance pId iId = do
  state@InstantiateMonad{polyTypes = pTs} <- get
  put state
    { polyTypes = Map.adjust (\pType -> pType{instances = iId `Set.insert` instances pType}) pId pTs
    }

class ReplacePolyTypes a where
  replacePolyTypes :: a -> IState (a, Map.Map Id Id)

instance ReplacePolyTypes CExtDecl where
  replacePolyTypes (CHMFDefExt (CHMFunDef chmHead (CFunDef cDeclSpecs cDeclr cDecls cStmt a) b)) = do
    replaceStmt <- replacePolyTypes (cStmt)
    let (cStmt', mapStmt) = replaceStmt
    return ((CHMFDefExt (CHMFunDef chmHead (CFunDef cDeclSpecs cDeclr cDecls cStmt' a) b)), mapStmt)

instance ReplacePolyTypes CStat where
  replacePolyTypes stmt@(CLabel _ _ _ _) = return (stmt, Map.empty)
  replacePolyTypes (CCase cExpr cStat a) = do
    replaceExpr <- replacePolyTypes cExpr
    replaceStmt <- replacePolyTypes cStat
    return
      ( CCase (fst replaceExpr) (fst replaceStmt) a
      , snd replaceExpr `Map.union` snd replaceStmt
      )
  replacePolyTypes (CCases _ _ _ _) = return $ error "case ranges not yet supported"  -- TODO: do cases
  replacePolyTypes (CDefault cStat a) = do
    replaceStat <- replacePolyTypes cStat
    return (CDefault (fst replaceStat) a, snd replaceStat)
  replacePolyTypes (CExpr (Just cExpr) a) = do
    replaceExpr <- replacePolyTypes cExpr
    return (CExpr (Just $ fst replaceExpr) a, snd replaceExpr)
  replacePolyTypes cExpr@(CExpr Nothing _) = return (cExpr, Map.empty)
  replacePolyTypes (CCompound labels blockItems a) = do
    replaceItems <- replacePolyTypes blockItems
    return (CCompound labels (fst replaceItems) a, snd replaceItems)
  replacePolyTypes (CIf cExpr cThen (Just cElse) a) = do
    replaceExpr <- replacePolyTypes cExpr
    replaceThen <- replacePolyTypes cThen
    replaceElse <- replacePolyTypes cElse
    return
      ( CIf (fst replaceExpr) (fst replaceThen) (Just (fst replaceElse)) a
      , snd replaceExpr `Map.union` snd replaceThen `Map.union` snd replaceElse
      )
  replacePolyTypes (CIf cExpr cThen Nothing a) = do
    replaceExpr <- replacePolyTypes cExpr
    replaceThen <- replacePolyTypes cThen
    return
      ( CIf (fst replaceExpr) (fst replaceThen) Nothing a
      , snd replaceExpr `Map.union` snd replaceThen
      )
  replacePolyTypes (CSwitch cExpr cStat a) = do
    replaceExpr <- replacePolyTypes cExpr
    replaceStmt <- replacePolyTypes cStat
    return
      ( CSwitch (fst replaceExpr) (fst replaceStmt) a
      , snd replaceExpr `Map.union` snd replaceStmt
      )
  replacePolyTypes (CWhile cExpr cStat doWhile a) = do
    replaceExpr <- replacePolyTypes cExpr
    replaceStmt <- replacePolyTypes cStat
    return
      ( CWhile (fst replaceExpr) (fst replaceStmt) doWhile a
      , snd replaceExpr `Map.union` snd replaceStmt
      )
  replacePolyTypes (CFor _ _ _ _ _) = return $ error "for is not yet supported"  -- TODO: do for
  replacePolyTypes cGoto@(CGoto _ _) = return (cGoto, Map.empty)
  replacePolyTypes cGotoPtr@(CGotoPtr _ _) = return (cGotoPtr, Map.empty)  -- TODO: well this is not right, right?
  replacePolyTypes cCont@(CCont _) = return (cCont, Map.empty)
  replacePolyTypes cBreak@(CBreak _) = return (cBreak, Map.empty)
  replacePolyTypes (CReturn (Just cExpr) a) = do
    replaceExpr <- replacePolyTypes cExpr
    return (CReturn (Just $ fst replaceExpr) a, snd replaceExpr)
  replacePolyTypes cAsm@(CAsm _ _) = return (cAsm, Map.empty)  -- TODO: todo or not todo

instance  ReplacePolyTypes CBlockItem where
  replacePolyTypes (CBlockStmt cStat) = do
    replaceStat <- replacePolyTypes cStat
    return (CBlockStmt $ fst replaceStat, snd replaceStat)

instance ReplacePolyTypes CExpr where
  replacePolyTypes (CComma cExprs a) = do
    replaceExprs <- traverse replacePolyTypes cExprs
    return (CComma (fst <$> replaceExprs) a, foldl1 Map.union (snd <$> replaceExprs))
  replacePolyTypes (CAssign assOp lExpr rExpr a) = do
    (lExpr', lMap) <- replacePolyTypes lExpr
    (rExpr', rMap) <- replacePolyTypes rExpr
    return (CAssign assOp lExpr' rExpr' a, lMap `Map.union` rMap)
  -- TODO: continue from here...


instance ReplacePolyTypes a => ReplacePolyTypes [a] where
  replacePolyTypes as = do
    replaceAs <- traverse replacePolyTypes as
    return (fst <$> replaceAs, foldl1 Map.union (snd <$> replaceAs))

instantiate :: CExtDecl -> Scheme -> IState [CExtDecl]
instantiate extFunDef scheme = do
  syncScopes
  (extFunDef', polyMap) <- replacePolyTypes extFunDef
  as <- parse extFunDef'
  InstantiateMonad{polyTypes = pTs} <- get
  children <- concat <$> sequence
    [ case name' `Map.lookup` polyMap of
        (Just name) -> case name `Map.lookup` pTs of
          (Just pType) ->
            if name' `Set.member` instances pType
            then addPolyTypeInstance name (name ++ mangleScheme scheme') >> instantiate (definition pType) scheme'
            else return []
          Nothing ->
            return $ error "this is weird, like really this should not happen.."
        Nothing -> return $ error "I don't know.. maybe not an error"
    | (name' :>: scheme') <- as
    ]
  return $ reverse (extFunDef' : children)

syncScopes :: IState ()
syncScopes = do
  state@InstantiateMonad{transformState = tS} <- get
  put state {lastScopeCopy = lastScope tS}

parse :: Transform a => a -> IState [Assump]
parse a = do
  state@InstantiateMonad{transformState = tS, parsedAssumps = pAs} <- get
  let (as, tS') = runState (typeInfer pAs a) tS
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
