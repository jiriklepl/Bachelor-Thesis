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
  , polyTypes :: Map.Map Id PolyType
  }

initInstantiateMonad :: InstantiateMonad
initInstantiateMonad = InstantiateMonad
  { parsedAssumps = []
  , transformState = initTransformMonad
  , polyTypes = Map.empty
  }

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
