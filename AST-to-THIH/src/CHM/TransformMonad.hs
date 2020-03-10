module CHM.TransformMonad
  ( TransformMonad(..)
  , TState
  , getTuple
  , getMember
  ) where

import Control.Monad.State
import qualified Data.Set as Set

import TypingHaskellInHaskell
import Language.C.Data
import Language.C.Syntax
import Language.C.Data.Ident (Ident(..))

data TransformMonad = TransformMonad
  { tuples :: Set.Set Int  -- memory of created tuple makers
  , createdClasses :: Set.Set Ident  -- memory of created member accessors
  , memberClasses :: EnvTransformer
  , builtIns :: [Assump]  -- all created symbols
  }

type TState = State TransformMonad

getTuple :: Int -> TState Id
getTuple n = do
  state@TransformMonad{tuples=ts, builtIns=bIs} <- get
  if n `Set.member` ts then
    return translate
  else do
    put state
      { tuples = n `Set.insert` ts
      , builtIns =
        ( translate :>:
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
    return translate
  where translate = "@make_tuple" ++ show n

-- getMember creates a member accessor
-- (if it doesn't exist, and its "@Has:X" class)
-- and returns its id
getMember :: Ident -> TState Id
getMember id@(Ident sId _ _) =
  let
    translateId = ".get:" ++ sId
    translateClass = "@Has:" ++ sId
    sVar = Tyvar "s" Star
    mVar = Tyvar "m" Star
    sTVar = TVar sVar
    mTVar = TVar mVar
  in do
    state@TransformMonad{createdClasses=cs,builtIns=bIs,memberClasses=mClasses} <- get
    if id `Set.member` cs then
      return translateId
    else do
      put state
        { memberClasses = mClasses
            <:> addClass translateClass []
        , builtIns =
          ( translateId :>:
            quantify [sVar, mVar]
            ([IsIn translateClass sTVar] :=> (sTVar `fn` mTVar))
          ): bIs
        , createdClasses = id `Set.insert` cs
        }
      return translateId
