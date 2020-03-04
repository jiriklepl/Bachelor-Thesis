module InstantiatorMonad where

import Control.Monad.State

data IState = IState
  { -- here go all the states
  }

data InstantiatorMonad = State IState

initState :: IState
initState = IState
  {
  }
