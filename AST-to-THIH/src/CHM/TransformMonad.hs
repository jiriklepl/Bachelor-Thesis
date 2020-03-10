module CHM.TransformMonad
  ( TransformMonad(..)
  , TState
  , getTuple
  ) where

import Control.Monad.State
import qualified Data.Set as Set

import TypingHaskellInHaskell

data TransformMonad = TransformMonad
  { tuples :: Set.Set Int
  , builtIns :: [Assump]
  }

type TState = State TransformMonad

getTuple :: Int -> TState Id
getTuple n = do
  state@TransformMonad{tuples=ts, builtIns=bIs} <- get
  if n `Set.member` ts then
    return (translate n)
  else do
    put state
      { tuples = n `Set.insert` ts
      , builtIns =
        ( translate n :>:
          let
            as = [Tyvar ("a" ++ show x) Star | x <- [1..n]]
          in quantify
            as
            ( [] :=>
              let
                tupleOperator =
                  TCon
                    ( Tycon
                      ("(" ++ replicate (n - 1) ',' ++ ")")
                      (last $ take 5 $ iterate (Kfun Star) Star)
                    )
              in foldr fn (foldl (\a b -> TAp a b) tupleOperator (TVar <$> as)) (TVar <$> as)
            )
        ) : bIs
      }
    return (translate n)
  where translate i = "make_tuple#" ++ show n
