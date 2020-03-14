module CHM.TransformMonad
  ( TransformMonad(..)
  , TState
  , tPointer
  , tConst
  , tError
  , mulOpFunc
  , divOpFunc
  , modOpFunc
  , addOpFunc
  , subOpFunc
  , shlOpFunc
  , shrOpFunc
  , xorOpFunc
  , orOpFunc
  , andOpFunc
  , logAndOpFunc
  , logOrOpFunc
  , eqOpFunc
  , neqOpFunc
  , ltOpFunc
  , gtOpFunc
  , leOpFunc
  , geOpFunc
  , assOpFunc
  , mulAssOpFunc
  , divAssOpFunc
  , modAssOpFunc
  , addAssOpFunc
  , subAssOpFunc
  , shlAssOpFunc
  , shrAssOpFunc
  , andAssOpFunc
  , xorAssOpFunc
  , orAssOpFunc
  , preIncOpFunc
  , postIncOpFunc
  , preDecOpFunc
  , postDecOpFunc
  , plusOpFunc
  , minusOpFunc
  , complOpFunc
  , negOpFunc
  , operatorFunction
  , commaOpFunc
  , ternaryOpFunc
  , elvisOpFunc
  , indexOpFunc
  , refFunc
  , derefFunc
  , ref
  , deref
  , pointer
  , findName
  , storeName
  , renameScoped
  , getSwitchName
  , enterScope
  , leaveScope
  , enterSwitch
  , leaveSwitch
  , getTupleOp
  , getTuple
  , getMember
  , runTState
  ) where

import Control.Monad.State
import qualified Data.Set as Set

import TypingHaskellInHaskell
import Language.C.Data
import Language.C.Syntax
import Language.C.Data.Ident (Ident(..))

type Scope = (Id, Int, Set.Set Id)

data TransformMonad = TransformMonad
  { tuples :: Set.Set Int  -- memory of created tuple makers
  , nested :: [Scope]  -- to avoid name collisions
  , switchScopes :: [Int]
  , lastScope :: Int
  , createdClasses :: Set.Set Ident  -- memory of created member accessors
  , memberClasses :: EnvTransformer
  , builtIns :: [Assump]  -- all created symbols
  }

type TState = State TransformMonad

tPointer :: Type
tConst :: Type
tError :: Type
tTuple3  :: Type


tPointer = TCon (Tycon "@Pointer" (Kfun Star Star))
tConst = TCon (Tycon "@Const" (Kfun Star Star))
tError = TCon (Tycon "@Error" Star)
tTuple3 = TCon (Tycon "(,,)" (Kfun Star (Kfun Star (Kfun Star Star))))

-- pointer reference & dereference functions
-- TODO: say something clever here
ref :: Expr -> Expr
deref :: Expr -> Expr
pointer :: Type -> Type
trio :: Type -> Type -> Type -> Type
fst3 :: (a, b, c) -> a

ref = Ap (Var refFunc)
deref = Ap (Var derefFunc)
pointer = TAp tPointer
trio a b c = TAp (TAp (TAp tTuple3 a) b) c
fst3 (a, b, c) = a

class OperatorFunction a where
  operatorFunction :: a -> Id

instance OperatorFunction CAssignOp where
  operatorFunction op = case op of
    CAssignOp -> assOpFunc
    CMulAssOp -> mulAssOpFunc
    CDivAssOp -> divAssOpFunc
    CRmdAssOp -> modAssOpFunc
    CAddAssOp -> addAssOpFunc
    CSubAssOp -> subAssOpFunc
    CShlAssOp -> shlAssOpFunc
    CShrAssOp -> shrAssOpFunc
    CAndAssOp -> andAssOpFunc
    CXorAssOp -> xorAssOpFunc
    COrAssOp -> orAssOpFunc

instance OperatorFunction CBinaryOp where
  operatorFunction op = case op of
    CMulOp -> mulOpFunc
    CDivOp -> divOpFunc
    CRmdOp -> modOpFunc
    CAddOp -> addOpFunc
    CSubOp -> subOpFunc
    CShlOp -> shlOpFunc
    CShrOp -> shrOpFunc
    CLeOp -> ltOpFunc
    CGrOp -> gtOpFunc
    CLeqOp -> leOpFunc
    CGeqOp -> geOpFunc
    CEqOp -> eqOpFunc
    CNeqOp -> neqOpFunc
    CAndOp -> andOpFunc
    CXorOp -> xorOpFunc
    COrOp -> orOpFunc
    CLndOp -> logAndOpFunc
    CLorOp -> logOrOpFunc

instance OperatorFunction CUnaryOp where
  operatorFunction op = case op of
    CPreIncOp -> preIncOpFunc
    CPreDecOp -> preDecOpFunc
    CPostIncOp -> postIncOpFunc
    CPostDecOp -> postDecOpFunc
    CAdrOp -> refFunc
    CIndOp -> derefFunc
    CPlusOp -> plusOpFunc
    CMinOp -> minusOpFunc
    CCompOp -> complOpFunc
    CNegOp -> negOpFunc

mulOpFunc     :: Id
divOpFunc     :: Id
modOpFunc     :: Id
addOpFunc     :: Id
subOpFunc     :: Id
shlOpFunc     :: Id
shrOpFunc     :: Id
xorOpFunc     :: Id
orOpFunc     :: Id
andOpFunc     :: Id
logAndOpFunc     :: Id
logOrOpFunc     :: Id

eqOpFunc      :: Id
neqOpFunc      :: Id
ltOpFunc      :: Id
gtOpFunc      :: Id
leOpFunc      :: Id
geOpFunc      :: Id

assOpFunc      :: Id
mulAssOpFunc      :: Id
divAssOpFunc      :: Id
modAssOpFunc      :: Id
addAssOpFunc      :: Id
subAssOpFunc      :: Id
shlAssOpFunc      :: Id
shrAssOpFunc      :: Id
andAssOpFunc      :: Id
xorAssOpFunc      :: Id
orAssOpFunc      :: Id

preIncOpFunc :: Id
postIncOpFunc :: Id
preDecOpFunc :: Id
postDecOpFunc :: Id
plusOpFunc :: Id
minusOpFunc :: Id
complOpFunc :: Id
negOpFunc :: Id

commaOpFunc   :: Id  -- takes two things and returns the second
ternaryOpFunc :: Id
elvisOpFunc   :: Id
indexOpFunc   :: Id
refFunc :: Id
derefFunc :: Id

mulOpFunc     = "*2"
divOpFunc     = "/2"
modOpFunc     = "%2"
addOpFunc     = "+2"
subOpFunc     = "-2"
shlOpFunc     = "<<2"  -- TODO
shrOpFunc     = ">>2"  -- TODO
xorOpFunc     = "^2"  -- TODO
orOpFunc     = "|2"  -- TODO
andOpFunc     = "&2"  -- TODO
logAndOpFunc     = "&&2"  -- TODO
logOrOpFunc     = "||2"  -- TODO

eqOpFunc      = "==2"
neqOpFunc      = "!=2"
ltOpFunc      = "<2"
gtOpFunc      = ">2"
leOpFunc      = "<=2"
geOpFunc      = ">=2"

assOpFunc      = "=2"
mulAssOpFunc      = "*=2"
divAssOpFunc      = "/=2"
modAssOpFunc      = "%=2"
addAssOpFunc      = "+=2"
subAssOpFunc      = "-=2"
shlAssOpFunc      = "<<=2"  -- TODO
shrAssOpFunc      = ">>=2"  -- TODO
andAssOpFunc      = "&=2"  -- TODO
xorAssOpFunc      = "^=2"  -- TODO
orAssOpFunc      = "|=2"  -- TODO

preIncOpFunc = "++1"  -- TODO
postIncOpFunc = "1++"  -- TODO
preDecOpFunc = "--1"  -- TODO
postDecOpFunc = "1--"  -- TODO
plusOpFunc = "+1"  -- TODO
minusOpFunc = "-1"  -- TODO
complOpFunc = "~1"  -- TODO
negOpFunc = "!1"  -- TODO

commaOpFunc   = ",2"
ternaryOpFunc = "?:3"
elvisOpFunc   = "?:2"
indexOpFunc   = "[]2"
refFunc       = "&1"
derefFunc     = "*1"

initTransformMonad :: TransformMonad
initTransformMonad = TransformMonad
  { tuples = Set.empty
  , createdClasses = Set.empty
  , nested = [("global",0,Set.empty)]
  , lastScope = 0
  , switchScopes = []
  , memberClasses =
    let
      aVar = Tyvar "a" Star
      bVar = Tyvar "b" Star
      aTVar = TVar aVar
      bTVar = TVar bVar
    in addClass "Add" []
    <:> addClass "Sub" []
    <:> addClass "Mul" []
    <:> addClass "Div" []
    <:> addClass "Mod" []  -- TODO
    <:> addClass "Eq" []
    <:> addClass "Eq0" []  -- TODO, for types that can compare to zero (like pointers and integral types)
    <:> addClass "LG" []
    <:> addClass "BinOp" []
    <:> addClass "LogOp" []
    <:> addInst [] (IsIn "Add" (pair tInt tInt))
    <:> addInst [] (IsIn "Add" (pair tFloat tFloat))
    <:> addInst [] (IsIn "Add" (pair tDouble tDouble))
    <:> addInst [] (IsIn "Add" (pair (pointer aTVar) (pointer bTVar)))
    <:> addInst [] (IsIn "Sub" (pair tInt tInt))
    <:> addInst [] (IsIn "Sub" (pair tFloat tFloat))
    <:> addInst [] (IsIn "Sub" (pair tDouble tDouble))
    <:> addInst [] (IsIn "Sub" (pair (pointer aTVar) (pointer bTVar)))
    <:> addInst [] (IsIn "Mul" (pair tInt tInt))
    <:> addInst [] (IsIn "Mul" (pair tFloat tFloat))
    <:> addInst [] (IsIn "Mul" (pair tDouble tDouble))
    <:> addInst [] (IsIn "Div" (pair tInt tInt))
    <:> addInst [] (IsIn "Div" (pair tFloat tFloat))
    <:> addInst [] (IsIn "Div" (pair tDouble tDouble))
    <:> addInst [] (IsIn "Mod" (pair tInt tInt))
    <:> addInst [] (IsIn "Eq"  (pair tInt tInt))
    <:> addInst [] (IsIn "Eq"  (pair tFloat tFloat))
    <:> addInst [] (IsIn "Eq"  (pair tDouble tDouble))
    <:> addInst [] (IsIn "Eq"  (pair (pointer aTVar) (pointer bTVar)))
    <:> addInst [] (IsIn "LG"  (pair tInt tInt))
    <:> addInst [] (IsIn "LG"  (pair tFloat tFloat))
    <:> addInst [] (IsIn "LG"  (pair tDouble tDouble))
    <:> addInst [] (IsIn "LG"  (pair (pointer aTVar) (pointer bTVar)))
    <:> addInst [] (IsIn "BinOp"  (pair tInt tInt))
    <:> addInst [] (IsIn "BinOp"  (pair (pointer aTVar) (pointer bTVar)))
  , builtIns =
    let
      aVar = Tyvar "a" Star
      bVar = Tyvar "b" Star
      aTVar = TVar aVar
      bTVar = TVar bVar
      aaaFuncWithClasses cs = quantify [aVar] (cs :=> (aTVar `fn` aTVar `fn` aTVar))
      abaFuncWithClasses cs = quantify [aVar, bVar] (cs :=> (aTVar `fn` bTVar `fn` aTVar))
      abBFuncWithClasses cs = quantify [aVar, bVar] (cs :=> (aTVar `fn` bTVar `fn` tBool))
    in
      [ addOpFunc :>: abaFuncWithClasses [IsIn "Add" (pair aTVar bTVar)]
      , subOpFunc :>: abaFuncWithClasses [IsIn "Sub" (pair aTVar bTVar)]
      , mulOpFunc :>: abaFuncWithClasses [IsIn "Mul" (pair aTVar bTVar)]
      , divOpFunc :>: abaFuncWithClasses [IsIn "Div" (pair aTVar bTVar)]
      , modOpFunc :>: abaFuncWithClasses [IsIn "Mod" (pair aTVar bTVar)]
      , assOpFunc :>: abBFuncWithClasses []
      , addAssOpFunc :>: abaFuncWithClasses [IsIn "Add" (pair aTVar bTVar)]
      , subAssOpFunc :>: abaFuncWithClasses [IsIn "Sub" (pair aTVar bTVar)]
      , mulAssOpFunc :>: abaFuncWithClasses [IsIn "Mul" (pair aTVar bTVar)]
      , divAssOpFunc :>: abaFuncWithClasses [IsIn "Div" (pair aTVar bTVar)]
      , modAssOpFunc :>: abaFuncWithClasses [IsIn "Mod" (pair aTVar bTVar)]
      , eqOpFunc :>: abBFuncWithClasses [IsIn "Eq" (pair aTVar bTVar)]
      , neqOpFunc :>: abBFuncWithClasses [IsIn "Eq" (pair aTVar bTVar)]
      , ltOpFunc :>: abBFuncWithClasses [IsIn "LG" (pair aTVar bTVar)]
      , gtOpFunc :>: abBFuncWithClasses [IsIn "LG" (pair aTVar bTVar)]
      , leOpFunc :>: abBFuncWithClasses [IsIn "LG" (pair aTVar bTVar), IsIn "Eq" (pair aTVar bTVar)]
      , geOpFunc :>: abBFuncWithClasses [IsIn "LG" (pair aTVar bTVar), IsIn "Eq" (pair aTVar bTVar)]
      , commaOpFunc :>: quantify [aVar, bVar] ([] :=> (aTVar `fn` bTVar `fn` bTVar))
      , ternaryOpFunc :>: quantify [aVar, bVar] ([] :=> (aTVar `fn` bTVar `fn` bTVar `fn` bTVar)) -- TODO: aTVar has to be 0 comparable
      , elvisOpFunc :>: quantify [aVar, bVar] ([] :=> (aTVar `fn` bTVar `fn` bTVar)) -- TODO: aTVar has to be 0 comparable
      , indexOpFunc :>: quantify [aVar, bVar] ([] :=> (pointer aTVar `fn` bTVar `fn` aTVar)) -- TODO: bTVar has to be integral
      , refFunc :>: quantify [aVar] ([] :=> (aTVar `fn` pointer aTVar))
      , derefFunc :>: quantify [aVar, bVar] ([] :=> (pointer aTVar `fn` aTVar))
      ]
  }

renameScoped :: Scope -> Id -> Id
renameScoped (name, count, _) id = name ++ show count ++ ':' : id

getSwitchName :: TState Id
getSwitchName = do
  TransformMonad{switchScopes=sScopes} <- get
  return $ "@Switch" ++ (show . head) sScopes

findName :: Id -> TState (Maybe Scope)
findName id = do
  TransformMonad{nested=ns} <- get
  let {
    recursiveSearch i [] = Nothing;
    recursiveSearch i (scope@(_, _, names):scopes) =
      if i `Set.member` names
      then
        Just scope
      else
        recursiveSearch i scopes
  } in return (recursiveSearch id ns)

storeName :: Id -> TState ()
storeName id = do
  state@TransformMonad{nested=ns} <- get
  case ns of
    (scopeId, count, names) : rest ->
      put state
        { nested = (scopeId, count, id `Set.insert` names) : rest
        }

enterScope :: Id -> TState ()
enterScope id = do
  state@TransformMonad{nested=ns, lastScope = n} <- get
  put state
    { nested = (if id == [] then fst3 (head ns) else id, n + 1, Set.empty) : ns
    , lastScope = n + 1
    }

leaveScope :: TState ()
leaveScope = do
  state@TransformMonad{nested=ns} <- get
  case ns of
    -- [top] -> leaving the global scope (-- TODO)
    _:rest ->
      put state
        { nested = rest
        }

-- implicitly enters new scope
enterSwitch :: TState ()
enterSwitch = do
  state@TransformMonad{nested=ns, lastScope = n, switchScopes = sScopes} <- get
  put state
    { nested = (fst3 (head ns), n + 1, Set.empty) : ns
    , lastScope = n + 1
    , switchScopes = (n + 1) : sScopes
    }

-- implicitly leaves current scope (+ should have the same relationship with enterSwitch as enter&leaveScope have)
leaveSwitch :: TState ()
leaveSwitch = do
  state@TransformMonad{nested=ns, switchScopes = sScopes} <- get
  case (ns, sScopes) of
    -- ([top], _) -> leaving the global scope (-- TODO)
    -- (_, []) -> leaving the top-most switch (-- TODO)
    (_:rest, s:ss) ->
      put state
        { nested = rest
        , switchScopes = ss
        }

getTupleOp :: Int -> Type
getTupleOp n =
  TCon
    ( Tycon
      ("(" ++ replicate (n - 1) ',' ++ ")")
      (last $ take 5 $ iterate (Kfun Star) Star)
    )

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
              foldr fn (foldl TAp (getTupleOp n) (TVar <$> as)) (TVar <$> as)
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

runTState :: TState a -> a
runTState a = (evalState a initTransformMonad)
