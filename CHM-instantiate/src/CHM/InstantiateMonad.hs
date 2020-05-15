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

data PolyType = PolyType CExtDecl (Set.Set Id)

data InstantiateMonad = InstantiateMonad
  { parsedAssumps :: [Assump]
  , transformState :: TransformMonad
  , lastScopeCopy :: Int
  , polyTypes :: Map.Map Id PolyType
  }

initInstantiateMonad :: InstantiateMonad
initInstantiateMonad = InstantiateMonad
  { parsedAssumps = []
  , transformState = initTransformMonad
  , lastScopeCopy = 0
  , polyTypes = Map.empty
  }

syncScopes :: IState ()
syncScopes = do
  state@InstantiateMonad{transformState = tS} <- get
  put state {lastScopeCopy = lastScope tS}

class ReLet a where
  reLet :: a -> (a, Program)

instance ReLet a => ReLet [a] where
  reLet as =
    let as' = reLet <$> as
    in (fst <$> as', concat $ snd <$> as')

instance ReLet Expr where
  reLet (Ap expr1 expr2) =
    let
      (expr1', program1) = reLet expr1
      (expr2', program2) = reLet expr2
    in (Ap expr1' expr2', program1 ++ program2)
  reLet (Let bindGroup expr) =
    let
      (bindGroup', program1) = reLet bindGroup
      (expr', program2) = reLet expr
    in (expr', program1 ++ program2)
  -- Var, Lit, Const
  reLet a = (a, [])

instance ReLet BindGroup where
  reLet (expls, impls) =
    let
      (expls', program1) = reLet expls
      (impls', program2) = reLet impls
    in ((expls', impls'), program1 ++ program2)

instance ReLet Expl where
  reLet (id, scheme, alts) =
    let (alts', program) = reLet alts
    in ((id, scheme, alts'), program)

instance ReLet Impl where
  reLet (id, alts) =
    let (alts', program) = reLet alts
    in ((id, alts'), program)

instance ReLet Alt where
  reLet (pats, expr) =
    let (expr', program) = reLet expr
    in ((pats, expr'), program)

parse :: Transform a => a -> IState [Assump]
parse a = do
  state@InstantiateMonad{transformState = tS, parsedAssumps = pAs} <- get
  let (as, tS') = runState (typeInfer pAs a) tS
  put state
    { transformState = tS'
    , parsedAssumps = as ++ pAs
    }
  return as

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
