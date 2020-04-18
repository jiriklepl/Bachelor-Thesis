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
  , returnFunc
  , caseFunc
  , ref
  , deref
  , pointer
  , findName
  , storeName
  , scopedName
  , getNextAnon
  , enterCHMHead
  , chmAddClass
  , chmAddVariable
  , leaveCHMHead
  , chmScheme
  , renameScoped
  , getSwitchName
  , getFunctionName
  , enterScope
  , leaveScope
  , enterSwitch
  , leaveSwitch
  , enterFunction
  , leaveFunction
  , addFunctionReturn
  , getFunctionReturns
  , getTupleOp
  , getTupleCon
  , getTuple
  , getMember
  , registerMember
  , runTState
  ) where

import Control.Monad.State
import qualified Data.Set as Set

import TypingHaskellInHaskell
import Language.C.Data
import Language.C.Syntax
import Language.C.Data.Ident (Ident(..))

data Scope = Scope
  { scopeName :: Id
  , scopeId :: Int
  , scopeVars :: Set.Set Id
  }
type ReturnExpr = Expr

initScope :: Id -> Int -> Scope
initScope name id = Scope
  { scopeName = name
  , scopeId = id
  , scopeVars = Set.empty
  }

data TransformMonad = TransformMonad
  { tuples :: Set.Set Int  -- memory of created tuple makers
  , nested :: [Scope]  -- to avoid name collisions
  , switchScopes :: [Int]
  , functionScopes :: [(Id, [ReturnExpr])]
  , lastScope :: Int
  , anonymousCounter :: Int
  , typeVariables :: [Set.Set Id]
  , variableClasses :: [[Pred]]
  , createdClasses :: Set.Set Id  -- memory of created member accessors
  , memberClasses :: EnvTransformer
  , builtIns :: Set.Set Assump  -- all created symbols
  }

type TState = State TransformMonad

tPointer :: Type
tConst :: Type
tError :: Type
tTuple3  :: Type


tPointer = TCon (Tycon "@Pointer" (Kfun Star Star))
tConst = TCon (Tycon "@Const" (Kfun Star Star))
tError = TCon (Tycon "@Error" Star)
tTuple3 = TCon (Tycon "(,,)3" (Kfun Star (Kfun Star (Kfun Star Star))))

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

returnFunc :: Id
caseFunc :: Id

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

returnFunc     = "@return"
caseFunc     = "@case"

initTransformMonad :: TransformMonad
initTransformMonad = TransformMonad
  { tuples = Set.empty
  , createdClasses = Set.empty
  , nested = [initScope "global" 0]
  , lastScope = 0
  , switchScopes = []
  , functionScopes = []
  , anonymousCounter = 0
  , typeVariables = [Set.empty]
  , variableClasses = [[]]
  , memberClasses =
    let
      aVar = Tyvar "a" Star
      bVar = Tyvar "b" Star
      aTVar = TVar aVar
      bTVar = TVar bVar
    -- all built-in classes (work in -- TODO)
    in  addClass "Num" []
    <:> addClass "Add" []
    <:> addClass "Sub" []
    <:> addClass "Mul" []
    <:> addClass "Div" []
    <:> addClass "Mod" []  -- TODO
    <:> addClass "Eq" []
    <:> addClass "Eq0" []  -- TODO, for types that can compare to zero (like pointers and integral types)
    <:> addClass "LG" []
    <:> addClass "BinOp" []
    <:> addClass "LogOp" []
    -- all built-in instances (work in -- TODO)
    <:> addInst [] (IsIn "Num" tInt)
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
      -- type variables
      aVar = Tyvar "a" Star
      bVar = Tyvar "b" Star
      -- variable types
      aTVar = TVar aVar
      bTVar = TVar bVar
      -- functions of the form 'a -> a -> a'
      aaaFuncWithClasses cs = quantify [aVar] (cs :=> (aTVar `fn` aTVar `fn` aTVar))
      -- functions of the form '(a, a) -> a'
      t2aaaFuncWithClasses cs = quantify [aVar] (cs :=> (tupledTypes [aTVar, aTVar] `fn` aTVar))
      -- functions of the form 'a -> a -> Void'
      aaVFuncWithClasses cs = quantify [aVar] (cs :=> (aTVar `fn` aTVar `fn` tVoid))
      -- functions of the form '(a, a) -> Void'
      t2aaVFuncWithClasses cs = quantify [aVar] (cs :=> (tupledTypes [aTVar, aTVar] `fn` tVoid))
      -- functions of the form 'a -> b -> a'
      abaFuncWithClasses cs = quantify [aVar, bVar] (cs :=> (aTVar `fn` bTVar `fn` aTVar))
      -- functions of the form '(a, b) -> a'
      t2abaFuncWithClasses cs = quantify [aVar, bVar] (cs :=> (tupledTypes [aTVar, bTVar] `fn` aTVar))
      -- functions of the form 'a -> b -> Bool'
      abBFuncWithClasses cs = quantify [aVar, bVar] (cs :=> (aTVar `fn` bTVar `fn` tBool))
      -- functions of the form '(a, b) -> Bool'
      t2abBFuncWithClasses cs = quantify [aVar, bVar] (cs :=> (tupledTypes [aTVar, bTVar] `fn` tBool))
    in Set.fromList
      [ addOpFunc :>: abaFuncWithClasses [IsIn "Add" (pair aTVar bTVar)]
      , subOpFunc :>: abaFuncWithClasses [IsIn "Sub" (pair aTVar bTVar)]
      , mulOpFunc :>: abaFuncWithClasses [IsIn "Mul" (pair aTVar bTVar)]
      , divOpFunc :>: abaFuncWithClasses [IsIn "Div" (pair aTVar bTVar)]
      , modOpFunc :>: abaFuncWithClasses [IsIn "Mod" (pair aTVar bTVar)]
      , assOpFunc :>: aaaFuncWithClasses []
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
      , derefFunc :>: quantify [aVar] ([] :=> (pointer aTVar `fn` aTVar))
      , returnFunc :>: aaaFuncWithClasses []
      , caseFunc :>: quantify [aVar] ([] :=> (aTVar `fn` aTVar `fn` tBool))
      ]
  }

renameScoped :: Scope -> Id -> Id
renameScoped Scope{scopeName = name, scopeId = n} id = name ++ show n ++ ':' : id

getSwitchName :: TState Id
getSwitchName = do
  TransformMonad{switchScopes = sScopes} <- get
  return $ "@Switch" ++ (show . head) sScopes

getFunctionName :: TState Id
getFunctionName = do
  TransformMonad{functionScopes = fScopes} <- get
  scopedName . fst . head $ fScopes

findName :: Id -> TState (Maybe Scope)
findName id = do
  TransformMonad{nested = ns} <- get
  let {
    recursiveSearch i [] = Nothing;
    recursiveSearch i (scope@Scope{scopeVars = names} : scopes) =
      if i `Set.member` names
      then
        Just scope
      else
        recursiveSearch i scopes
  } in return (recursiveSearch id ns)

storeName :: Id -> TState ()
storeName id = do
  state@TransformMonad{nested = ns} <- get
  case ns of
    scope@Scope{scopeVars = names} : rest ->
      put state
        { nested = scope{scopeVars = id `Set.insert` names} : rest
        }

scopedName :: Id -> TState Id
scopedName id = do
  scope <- findName id
  case scope of
    Just s -> return $ renameScoped s id
    _ -> return $ "@Error:" ++ id

getNextAnon :: TState Int
getNextAnon = do
  state@TransformMonad{anonymousCounter = i} <- get
  put state {anonymousCounter = i + 1}
  return i

enterCHMHead :: TState ()
enterCHMHead = do
  state@TransformMonad{variableClasses=vs,typeVariables=ts} <- get
  put state
    { variableClasses = [] : vs
    , typeVariables = Set.empty : ts
    }

chmAddVariable :: Id -> TState ()
chmAddVariable id = do
  state@TransformMonad{typeVariables=ts} <- get
  case ts of
    t:rest -> put state
      { typeVariables = (id `Set.insert` t) : rest
      }
    _ -> return . error $ "not in chm block"

chmAddClass :: Pred -> TState ()
chmAddClass p = do
  state@TransformMonad{variableClasses=cs} <- get
  case cs of
    c:rest -> put state
      { variableClasses = (p : c) : rest
      }
    _ -> return . error $ "not in chm block"

leaveCHMHead :: TState ()
leaveCHMHead = do
  state@TransformMonad{variableClasses=vs,typeVariables=ts} <- get
  put state
    { variableClasses = tail vs
    , typeVariables = tail ts
    }

-- filterTypes takes a 'type' and a set of 'unfiltered' and return 'filtered'
-- which contains the types from the 'unfiltered' set that contribute
-- towards the 'type'
filterTypes :: Type -> Set.Set Id -> ([Tyvar], Set.Set Id)
filterTypes t tSet
  | tSet == Set.empty = ([], Set.empty)
  | otherwise = case t of
    TAp t1 t2 ->
      let
        (ts, tSet') = filterTypes t1 tSet
        (tsFinal, tSetFinal) = filterTypes t2 tSet'
      in
        (ts ++ tsFinal, tSetFinal)
    TVar tv@(Tyvar id _) -> if id `Set.member` tSet
      then ([tv], id `Set.delete` tSet)
      else ([], tSet)
    _ -> ([], tSet)

depends :: Type -> [Tyvar] -> Bool
depends (TVar t@(Tyvar id _)) ts = t `elem` ts
depends (TAp t1 t2) ts
  =  depends t2 ts
  || depends t1 ts
depends _ ts = False

filterClasses :: [Tyvar] -> [Pred] -> [Pred]
filterClasses ts (pred@(IsIn id t):preds) = if depends t ts
  then pred : filterClasses ts preds
  else filterClasses ts preds
filterClasses _ [] = []

chmScheme :: Type -> TState Scheme
chmScheme t = do
  state@TransformMonad
    { typeVariables = tvs
    , variableClasses = vcs
    } <- get
  let {
    (types, _) = filterTypes t $ head tvs;
    classes = filterClasses types $ head vcs
  } in return $ quantify types $ classes :=> t

enterScope :: Id -> TState ()
enterScope id = do
  state@TransformMonad{nested = ns, lastScope = n} <- get
  put state
    { nested =
        initScope
          (if null id
              then scopeName (head ns)
              else id)
          (n + 1)
        : ns
    , lastScope = n + 1
    }

leaveScope :: TState ()
leaveScope = do
  state@TransformMonad{nested = ns} <- get
  put state
    { nested = tail ns
    }

-- implicitly enters new scope
enterSwitch :: TState ()
enterSwitch = do
  enterScope ""
  state@TransformMonad{lastScope = n, switchScopes = sScopes} <- get
  put state
    { switchScopes = (n + 1) : sScopes
    }

-- implicitly leaves current scope (+ should have the same relationship with enterSwitch as enter&leaveScope have)
leaveSwitch :: TState ()
leaveSwitch = do
  leaveScope
  state@TransformMonad{switchScopes = sScopes} <- get
  put state
    { switchScopes = tail sScopes
    }

-- implicitly enters new scope
enterFunction :: Id -> TState ()
enterFunction id = do
  enterScope id
  state@TransformMonad{lastScope = n, functionScopes = fScopes} <- get
  put state
    { functionScopes = (id, []) : fScopes
    }

-- implicitly leaves current scope (+ should have the same relationship with enterFunction as enter&leaveScope have)
leaveFunction :: TState ()
leaveFunction = do
  leaveScope
  state@TransformMonad{functionScopes = fScopes} <- get
  put state
    { functionScopes = tail fScopes
    }

addFunctionReturn :: ReturnExpr -> TState ()
addFunctionReturn fReturn = do
  state@TransformMonad{functionScopes = fScopes} <- get
  case fScopes of
    -- [] -> no active function
    (id, fReturns):rest -> put state
      {
        functionScopes = (id, fReturn : fReturns) : rest
      }

getFunctionReturns :: TState [ReturnExpr]
getFunctionReturns = do
  TransformMonad{functionScopes = fScopes} <- get
  return . snd . head $ fScopes

getTupleOp :: Int -> Type
getTupleOp n =
  TCon
    ( Tycon
      ("(" ++ replicate (n - 1) ',' ++ ")" ++ show n)
      (last $ take (n + 1) $ iterate (Kfun Star) Star)
    )

tupledTypes :: [Type] -> Type
tupledTypes ts = foldl TAp (getTupleOp . length $ ts) ts

tupleize :: [Type] -> Type
tupleize ts = foldr fn (tupledTypes ts) ts

getTupleCon :: Int -> Scheme
getTupleCon n =
  let
    as = [Tyvar ("a" ++ show x) Star | x <- [1..n]]
  in
    quantify as ([] :=> tupleize (TVar <$> as))

getTuple :: Int -> TState Id
getTuple n = do
  state@TransformMonad{tuples=ts, builtIns=bIs} <- get
  if n `Set.member` ts then
    return translate
  else do
    put state
      { tuples = n `Set.insert` ts
      , builtIns =
        (translate :>: getTupleCon n) `Set.insert` bIs
      }
    return translate
  where translate = "@make_tuple" ++ show n

-- getMember creates a member accessor
-- (if it doesn't exist, and its "@Has:X" class)
-- and returns its id

memberClassName :: Id -> Id
memberClassName id = "@Has:" ++ id

memberGetterName :: Id -> Id
memberGetterName id = ".get:" ++ id

getMember :: Ident -> TState Id
getMember id@(Ident sId _ _) = return $ memberGetterName sId

-- registers a member getter for the given struct and its member
-- expressed via their ids respectively,
-- creates the member's getter class if it doesn't exist
registerMember :: Id -> Id -> Type -> TState ()
registerMember sId mId t =
  let
    sVar = Tyvar "structVar" Star
    sTVar = TVar sVar
    mClassName = memberClassName mId
    sCon = TCon (Tycon sId Star)
  in do
    state@TransformMonad{createdClasses=cs,builtIns=bIs,memberClasses=mClasses} <- get
    if mId `Set.member` cs then
      put state
        { memberClasses = mClasses
            <:> addInst [] (IsIn mClassName sCon)
        }
    else
      put state
        { memberClasses = mClasses
            <:> addClass mClassName []
            <:> addInst [] (IsIn mClassName sCon)
        , builtIns =
          ( memberGetterName mId :>:
            quantify [sVar]
            ([IsIn mClassName sTVar] :=> (sTVar `fn` t))
          ) `Set.insert` bIs
        , createdClasses = mId `Set.insert` cs
        }

runTState :: TState a -> (a,TransformMonad)
runTState a = runState a initTransformMonad
