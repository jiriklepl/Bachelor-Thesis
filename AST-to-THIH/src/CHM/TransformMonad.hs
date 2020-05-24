{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module CHM.TransformMonad
  ( MethodNamed
  , Method(..)
  , TransformMonad(..)
  , GetCName(..)
  , GetSU(..)
  , TState
  , initTransformMonad
  , getClassMethods
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
  , sgName
  , getNextAnon
  , appendNextAnon
  , enterCHMHead
  , chmAddVariable
  , chmAddAlias
  , chmAddClass
  , leaveCHMHead
  , replaceAliases
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
  , takeNKind
  , getTupleOp
  , tupleize
  , getTupleCon
  , getTuple
  , getMember
  , registerMember
  , registerCHMMember
  , createParamsType
  , registerStruct
  , getStructKind
  , registerClass
  , registerClassDeclaration
  , getMethodScheme
  , registerMethodInstance
  , runTState
  ) where

import Control.Monad.State
import Data.List
import qualified Data.Set as Set
import qualified Data.Map as Map

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

data Method = Method
  { methodScheme :: Scheme
  , methodInstances :: Set.Set Type
  }

initMethod :: Scheme -> Method
initMethod s = Method
  { methodScheme = s
  , methodInstances = Set.empty
  }

data Struct = Struct
  { structKind :: Kind
  }

data UserClass = UserClass
  { methods :: Map.Map Id Method
  }

type MethodNamed = (Id, Method)

getClassMethods :: UserClass -> [(Id, Method)]
getClassMethods = Map.toList . methods

initUserClass :: UserClass
initUserClass = UserClass
  { methods = Map.empty
  }

data TransformMonad = TransformMonad
  { tuples :: Set.Set Int
    -- ^ memory of created tuple makers
  , nested :: [Scope]
    -- ^ to avoid name collisions
  , switchScopes :: [Int]
    {- ^
      remembers the number of the scope of a switch statement
      to connect it to its cases (we can have while in a switch etc.)
      recursively
    -}
  , functionScopes :: [(Id, [ReturnExpr])]
    {- ^
      This is used for naming of nested variables and for connecting
      return statements to their functions
    -}
  , lastScope :: Int
    -- ^ the number of the last created scope
  , registeredStructs :: Map.Map Id Struct
    -- ^ names of all created structs
  , anonymousCounter :: Int
    -- ^ number of the NEXT anonymous variable
  , userClasses :: Map.Map Id UserClass
    -- ^ map of all created user classes and their methods
  , typeVariables :: [[Tyvar]]
    -- ^ type variables declared in chm heads
  , typeAliases :: [Map.Map Id Type]
    -- ^ types that are actually aliases in chm heads
  , variableClasses :: [[Pred]]
    -- ^ class constraints over variables in chm heads
  , createdClasses :: Set.Set Id
    -- ^ memory of created member accessors
  , memberClasses :: EnvTransformer
    -- ^ all classes and their instances
  , builtIns :: Set.Set Assump
    -- ^ all created symbols
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
trio = (TAp .) . TAp . TAp tTuple3
fst3 (a, _, _) = a

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
orOpFunc      :: Id
andOpFunc     :: Id
logAndOpFunc  :: Id
logOrOpFunc   :: Id

eqOpFunc      :: Id
neqOpFunc     :: Id
ltOpFunc      :: Id
gtOpFunc      :: Id
leOpFunc      :: Id
geOpFunc      :: Id

assOpFunc     :: Id
mulAssOpFunc  :: Id
divAssOpFunc  :: Id
modAssOpFunc  :: Id
addAssOpFunc  :: Id
subAssOpFunc  :: Id
shlAssOpFunc  :: Id
shrAssOpFunc  :: Id
andAssOpFunc  :: Id
xorAssOpFunc  :: Id
orAssOpFunc   :: Id

preIncOpFunc  :: Id
postIncOpFunc :: Id
preDecOpFunc  :: Id
postDecOpFunc :: Id
plusOpFunc    :: Id
minusOpFunc   :: Id
complOpFunc   :: Id
negOpFunc     :: Id

-- takes two things and returns the second
commaOpFunc   :: Id
ternaryOpFunc :: Id
elvisOpFunc   :: Id
indexOpFunc   :: Id
refFunc       :: Id
derefFunc     :: Id

returnFunc    :: Id
caseFunc      :: Id

{-
  Operators follow a naming convention where there is
  the operator itself followed by the number of its operands
  (with notable exception where we have to distinguish the
  pre-increment and post-increment operators)

  This naming convention ensures the names are simple enough
  and that they resemble their appearance in the code while
  giving unique names to their unary and binary counterparts
-}

mulOpFunc     = "*2"
divOpFunc     = "/2"
modOpFunc     = "%2"
addOpFunc     = "+2"
subOpFunc     = "-2"
shlOpFunc     = "<<2"  -- TODO
shrOpFunc     = ">>2"  -- TODO
xorOpFunc     = "^2"  -- TODO
orOpFunc      = "|2"  -- TODO
andOpFunc     = "&2"  -- TODO
logAndOpFunc  = "&&2"  -- TODO
logOrOpFunc   = "||2"  -- TODO

eqOpFunc      = "==2"
neqOpFunc     = "!=2"
ltOpFunc      = "<2"
gtOpFunc      = ">2"
leOpFunc      = "<=2"
geOpFunc      = ">=2"

assOpFunc     = "=2"
mulAssOpFunc  = "*=2"
divAssOpFunc  = "/=2"
modAssOpFunc  = "%=2"
addAssOpFunc  = "+=2"
subAssOpFunc  = "-=2"
shlAssOpFunc  = "<<=2"  -- TODO
shrAssOpFunc  = ">>=2"  -- TODO
andAssOpFunc  = "&=2"  -- TODO
xorAssOpFunc  = "^=2"  -- TODO
orAssOpFunc   = "|=2"  -- TODO

preIncOpFunc  = "++1"  -- TODO
postIncOpFunc = "1++"  -- TODO
preDecOpFunc  = "--1"  -- TODO
postDecOpFunc = "1--"  -- TODO
plusOpFunc    = "+1"  -- TODO
minusOpFunc   = "-1"  -- TODO
complOpFunc   = "~1"  -- TODO
negOpFunc     = "!1"  -- TODO

commaOpFunc   = ",2"
ternaryOpFunc = "?:3"
elvisOpFunc   = "?:2"
indexOpFunc   = "[]2"
refFunc       = "&1"
derefFunc     = "*1"

returnFunc    = "@return"
caseFunc      = "@case"

initTransformMonad :: TransformMonad
initTransformMonad =
  let
    aVar = Tyvar "a" Star
    bVar = Tyvar "b" Star
    aTVar = TVar aVar
    bTVar = TVar bVar
  in TransformMonad
    { tuples = Set.empty
    , createdClasses = Set.empty
    , nested = [initScope "global" 0]
    , lastScope = 0
    , registeredStructs = Map.empty
    , switchScopes = []
    , functionScopes = []
    , anonymousCounter = 0
    , userClasses = Map.empty
    , typeVariables = []
    , typeAliases = []
    , variableClasses = []
    , memberClasses =
      -- all built-in classes (work in -- TODO)
      addClass "Num" []
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
      <:> addInst [] (IsIn "Add" tInt)
      <:> addInst [] (IsIn "Add" (pair tFloat tFloat))
      <:> addInst [] (IsIn "Add" (pair tDouble tDouble))
      <:> addInst [] (IsIn "Add" (pair (pointer aTVar) (pointer bTVar)))
      <:> addInst [] (IsIn "Sub" (pair tInt tInt))
      <:> addInst [] (IsIn "Sub" (pair tFloat tFloat))
      <:> addInst [] (IsIn "Sub" (pair tDouble tDouble))
      <:> addInst [] (IsIn "Sub" (pair (pointer aTVar) (pointer bTVar)))
      <:> addInst [] (IsIn "Mul" tInt)
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
        [ addOpFunc :>: aaaFuncWithClasses [IsIn "Add" aTVar]  -- TODO: all arithmetics
        , subOpFunc :>: abaFuncWithClasses [IsIn "Sub" (pair aTVar bTVar)]
        , mulOpFunc :>: aaaFuncWithClasses [IsIn "Mul" aTVar]
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

-- | Renames a variable's name depending on which scope we are currently parsing
renameScoped :: Scope -> Id -> Id
renameScoped Scope{scopeName = name, scopeId = n} id =
  if n == 0
    then id
    else name ++ show n ++ ':' : id

-- | Gets the name of the current switch statement
getSwitchName :: TState Id
getSwitchName = do
  TransformMonad{switchScopes = sScopes} <- get
  return $ "@Switch" ++ (show . head) sScopes

-- | Gets the name of the current function
getFunctionName :: TState Id
getFunctionName = do
  TransformMonad{functionScopes = fScopes} <- get
  scopedName . fst . head $ fScopes

findName :: Id -> TState (Maybe Scope)
findName id = do
  TransformMonad{nested = ns} <- get
  let
    recursiveSearch i [] = Nothing
    recursiveSearch i (scope@Scope{scopeVars = names} : scopes) =
      if i `Set.member` names
      then
        Just scope
      else
        recursiveSearch i scopes
  return (recursiveSearch id ns)

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

sgName :: Id -> TState Id
sgName id = storeName id >> scopedName id

getNextAnon :: TState Int
getNextAnon = do
  state@TransformMonad{anonymousCounter = i} <- get
  put state {anonymousCounter = i + 1}
  return i

appendNextAnon :: Id -> TState Id
appendNextAnon id = (id ++) . show <$> getNextAnon

enterCHMHead :: TState ()
enterCHMHead = do
  state@TransformMonad
    { variableClasses = vCs
    , typeVariables = tVs
    , typeAliases = tAs
    } <- get
  put state
    { variableClasses = [] : vCs
    , typeVariables = [] : tVs
    , typeAliases = Map.empty : tAs
    }

chmAddVariable :: Tyvar -> TState ()
chmAddVariable tyvar = do
  state@TransformMonad{typeVariables = tVs} <- get
  case tVs of
    ts:rest -> put state{typeVariables = (tyvar : ts) : rest}
    _ -> return . error $ "not in chm head block"

chmAddAlias :: Id -> Type -> TState ()
chmAddAlias id t = do
  state@TransformMonad{typeAliases = tAs} <- get
  case tAs of
    tas:restA -> put state
      { typeAliases = Map.insert id t tas : restA
      }
    _ -> return . error $ "not in chm head block"

chmAddClass :: Pred -> TState ()
chmAddClass p = do
  state@TransformMonad{variableClasses = cs} <- get
  case cs of
    c:rest -> put state{variableClasses = (p : c) : rest}
    _ -> return . error $ "not in chm head block"

leaveCHMHead :: TState ()
leaveCHMHead = do
  state@TransformMonad
    { variableClasses = vCs
    , typeVariables = tVs
    , typeAliases = tAs
    } <- get
  put state
    { variableClasses = tail vCs
    , typeVariables = tail tVs
    , typeAliases = tail tAs
    }

-- | Takes a 'Type' and then -- TODO: god I am tired for this
filterTypes :: Type -> (Set.Set Tyvar, Set.Set Id) -> (Set.Set Tyvar, Set.Set Id)
filterTypes t accumulator@(tSet, idSet)
  | idSet == Set.empty = accumulator
  | otherwise = case t of
    TAp t1 t2 -> filterTypes t2 . filterTypes t1 $ accumulator
    TVar tv@(Tyvar id _) -> if id `Set.member` idSet
      then (tv `Set.insert` tSet, id `Set.delete` idSet)
      else accumulator
    _ -> accumulator

-- | Returns whether the given Type depends on any of the given type variables
depends :: Type -> Set.Set Tyvar -> Bool
depends (TVar t@(Tyvar id _)) ts = t `Set.member` ts
depends (TAp t1 t2) ts
  =  depends t2 ts
  || depends t1 ts
depends _ ts = False

addTypesFromType :: Type -> Set.Set Tyvar -> Set.Set Tyvar
addTypesFromType (TVar t@(Tyvar id _)) ts = t `Set.insert` ts
addTypesFromType (TAp t1 t2) ts =
  addTypesFromType t1 . addTypesFromType t2 $ ts
addTypesFromType _ ts = ts

filterClasses :: (Set.Set Tyvar, [Pred], [Pred]) -> (Set.Set Tyvar, [Pred], [Pred])
filterClasses acc@(_, [], _) = acc
filterClasses acc@(tVars, preds, outPreds) =
  case partition (\(IsIn _ t) -> depends t tVars) preds of
    ([], _) -> acc
    (preds', preds'') ->
      let tVars' = foldr ($) tVars [addTypesFromType t | IsIn _ t <- preds']
      in filterClasses (tVars', preds'', preds' ++ outPreds)

-- | Replaces aliases created in the last chm head by real type variables
replaceAliases :: Type -> TState Type
replaceAliases t@(TVar (Tyvar id kind)) = do
  TransformMonad{typeAliases = tAs} <- get
  case id `Map.lookup` head tAs of
    Just t' -> return t'
    Nothing -> return t
replaceAliases (TAp t1 t2) = do
  t1' <- replaceAliases t1
  t2' <- replaceAliases t2
  return $ TAp t1' t2'
-- for TGen(?) and mainly TCon
replaceAliases t = return t

-- | Replaces type annotations with generic types and constraints (see 'quantify')
chmScheme :: Type -> TState Scheme
chmScheme t = do
  state@TransformMonad
    { typeVariables = tVs
    , variableClasses = vCs
    } <- get
  t' <- replaceAliases t
  let
    tVars = Set.fromList [id | Tyvar id _ <- head tVs]
    (types, _) = filterTypes t' (Set.empty, tVars)
    (types', _, classes) = filterClasses (types, head vCs, [])
  return $ quantify (Set.toList types') $ classes :=> t'
{-
chmScheme :: Type -> TState Scheme
chmScheme t = do
  tVs <- gets typeVariables
  vCs <- gets variableClasses
  t' <- replaceAliases t
  return $ quantify (head tVs) (head vCs :=> t')
-}
-- | Enters a new 'Scope' (c scope)
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

-- | Leaves the currently parsed 'Scope'
leaveScope :: TState ()
leaveScope = do
  state@TransformMonad{nested = ns} <- get
  put state
    { nested = tail ns
    }

-- | Enters a new switch statement and implicitly enters a new 'Scope'
enterSwitch :: TState ()
enterSwitch = do
  enterScope ""
  state@TransformMonad{lastScope = n, switchScopes = sScopes} <- get
  put state
    { switchScopes = (n + 1) : sScopes
    }

-- | Leaves the current switch statement block and implicitly leaves the current 'Scope'
leaveSwitch :: TState ()
leaveSwitch = do
  leaveScope
  state@TransformMonad{switchScopes = sScopes} <- get
  put state
    { switchScopes = tail sScopes
    }

-- | Enters a new function and implicitly enters a new 'Scope'
enterFunction :: Id -> TState ()
enterFunction id = do
  enterScope id
  state@TransformMonad{lastScope = n, functionScopes = fScopes} <- get
  put state
    { functionScopes = (id, []) : fScopes
    }

-- | Leaves the current function and implicitly leaves the current 'Scope'
leaveFunction :: TState ()
leaveFunction = do
  leaveScope
  state@TransformMonad{functionScopes = fScopes} <- get
  put state
    { functionScopes = tail fScopes
    }

-- | Adds a new return expression of the currently parsed function
addFunctionReturn :: ReturnExpr -> TState ()
addFunctionReturn fReturn = do
  state@TransformMonad{functionScopes = fScopes} <- get
  case fScopes of
    -- [] -> no active function
    (id, fReturns):rest -> put state
      {
        functionScopes = (id, fReturn : fReturns) : rest
      }

-- | Gets all stored return expressions of the currently parsed function
getFunctionReturns :: TState [ReturnExpr]
getFunctionReturns = do
  TransformMonad{functionScopes = fScopes} <- get
  return . snd . head $ fScopes

-- | Creates the simplest kind of type constructor that can take n types
takeNKind :: Int -> Kind
takeNKind n = last $ take (n + 1) $ iterate (Kfun Star) Star

-- | Returns the tuple type constructor of the specified number of types
getTupleOp :: Int -> Type
getTupleOp n =
  TCon
    ( Tycon
        ("(" ++ replicate (n - 1) ',' ++ ")" ++ show n)
        (takeNKind n)
    )

-- | Transforms a list of types to a tuple (see 'getTupleOp')
tupledTypes :: [Type] -> Type
tupledTypes ts = foldl TAp (getTupleOp . length $ ts) ts

-- | Returns a function that takes the specified 'Type's
-- and returns a tuple of them (see 'tupleTypes')
tupleize :: [Type] -> Type
tupleize ts = foldr fn (tupledTypes ts) ts

-- | Returns the 'Scheme' of a tuple constructor that takes 'Int' 'Type's
getTupleCon :: Int -> Scheme
getTupleCon n =
  let
    as = [Tyvar ("a" ++ show x) Star | x <- [1..n]]
  in
    quantify as ([] :=> tupleize (TVar <$> as))

-- | Returns a function that creates a tuple of 'Int' variables
-- creates it if called for the first time
getTuple :: Int -> TState Id
getTuple n = do
  state@TransformMonad{tuples = ts, builtIns = bIs} <- get
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

-- | Creates a new name for the type class of the getter/setter of the member field
memberClassName :: Id -> Id
memberClassName id = "Has_" ++ id

-- | This has to be named so that it cannot collide with
-- other user-defined functions
memberGetterName :: Id -> Id
memberGetterName id = ".get:" ++ id

-- 'getMember' creates a member accessor
-- (if it doesn't exist, and its "@Has_X" class)
-- and returns its id
getMember :: Ident -> TState Id
getMember id@(Ident sId _ _) = return $ memberGetterName sId

-- registers a member getter for the given struct and its member
-- expressed via their ids respectively,
-- creates the member's getter class if it doesn't exist
registerMember :: Id -> Id -> Type -> TState ()
registerMember sId mId t = do
  state@TransformMonad
    { createdClasses = cs
    , builtIns = bIs
    , memberClasses = mClasses
    } <- get
  let
    sVar = Tyvar "structVar" Star
    sTVar = TVar sVar
    mClassName = memberClassName mId
    sCon = TCon (Tycon sId Star)
    getter = memberGetterName mId :>:
        quantify [sVar]
        ([IsIn mClassName sTVar] :=> (sTVar `fn` t))
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
      , builtIns = getter `Set.insert` bIs
      , createdClasses = mId `Set.insert` cs
      }

-- | creates a getter/setter for a given member field of a struct with a specified type
registerCHMMember :: Id -> Id -> Type -> TState ()
registerCHMMember sId mId t = do
  state@TransformMonad
    { createdClasses = cs
    , builtIns = bIs
    , memberClasses = mClasses
    , typeVariables = tVs
    , typeAliases = tAs
    , variableClasses = vCs
    } <- get
  let
    mClassName = memberClassName mId
    tVars = TVar <$> head tVs
    sKind = takeNKind $ length tVars
    sVar = Tyvar "structVar" sKind
    sTVar = foldl TAp (TVar sVar) tVars
    sCon = foldl TAp (TCon (Tycon sId sKind)) tVars
    getter = memberGetterName mId :>:
      quantify
        (sVar : head tVs)
        ((IsIn mClassName sTVar : head vCs) :=> (sTVar `fn` t))
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
      , builtIns = getter `Set.insert` bIs
      , createdClasses = mId `Set.insert` cs
      }

-- | Creates a tuple of parameter types if there is a multiple of them,
-- if there is only one, returns it without creating a tuple
createParamsType :: [Type] -> Type
createParamsType [t] = t
createParamsType ts = foldl TAp (getTupleOp $ length ts) ts

-- | Makes a new entry for the given struct in the 'TransformMonad'
registerStruct :: Id -> TState Bool
registerStruct id = do
  state@TransformMonad{registeredStructs = rSs, typeVariables = tVs} <- get
  if id `Map.member` rSs then
    return False
  else do
    put state
      { registeredStructs =
          Map.insert
            id
            Struct
              { structKind =
                  if null tVs
                    then Star
                    else takeNKind (length $ head tVs)
              }
            rSs
      }
    return True

-- | returns the kind of a struct
getStructKind :: Id -> TState Kind
getStructKind id =
  gets (structKind . (Map.! id) . registeredStructs)

-- | Makes a new entry in the class environment and in the 'TransformMonad'
registerClass :: Id -> TState Bool
registerClass id = do
  state@TransformMonad
    { userClasses = uCs
    , typeVariables = tVs
    , variableClasses = vCs
    , memberClasses = mCs
    } <- get
  if id `Map.member` uCs then
    -- there is no new class entry as it would make an collision
    return False
  else do
    let
      tVars = head tVs
      count = length tVars
      classType = createParamsType $ TVar <$> tVars
      superClasses =
        [ if t /= classType
          then error "invalid superclass"  -- super-class has to have the same parameter(s)
          else name
        | IsIn name t <- head vCs
        ]
    put state
      { userClasses = Map.insert id initUserClass uCs  -- we add a new entry for the class
      , variableClasses = [IsIn id classType] : tail vCs  -- we replace all constraints with the class
      , memberClasses = mCs
          <:> addClass id superClasses  -- we add an entry to the class environment
      }
    -- a class entry was actually created
    return True

-- | Registers the 'Assump' of a declaration in a class
registerClassDeclaration :: Id -> Assump -> TState ()
registerClassDeclaration cId (mId :>: scheme) = do
  state@TransformMonad{userClasses=uCs} <- get
  put state
    { userClasses = Map.adjust (\uClass -> uClass{methods = Map.insert mId (initMethod scheme) (methods uClass)}) cId uCs
    }

-- | Returns 'Just' the 'Scheme' of a method of a class specified by their 'Id's
-- or returns 'Nothing' if lookup of either of those fails
getMethodScheme :: Id -> Id -> TState (Maybe Scheme)
getMethodScheme cId mId = do
  state@TransformMonad{userClasses=uCs} <- get
  return $ methodScheme <$> (Map.lookup mId =<< methods <$> Map.lookup cId uCs)

mangleName :: Id -> Type -> TState Id
mangleName id mType = do
  num <- getNextAnon
  return $ id ++ '_' : show num  -- TODO

registerMethodInstance :: Id -> Id -> Type -> TState Id
registerMethodInstance cId mId mType = do
  state@TransformMonad{userClasses=uCs, memberClasses=mCs} <- get
  name <- mangleName mId mType
  put state
    { userClasses =
        Map.adjust
          (\uClass -> uClass
            { methods =
                Map.adjust
                  (\method -> method
                    { methodInstances =
                        let instances = methodInstances method
                        in
                          if mType `Set.member` instances
                          then error "method's instance already defined"
                          else mType `Set.insert` instances
                    }
                  )
                  mId
                  (methods uClass)
            }
          )
          cId
          uCs
    , memberClasses = mCs
        <:> addInst [] (IsIn cId mType)
    }
  return name

runTState :: TState a -> (a,TransformMonad)
runTState a = runState a initTransformMonad

class GetCName a where
  getCName :: a -> Id

instance GetCName CFunDef where
  getCName (CFunDef _ (CDeclr (Just (Ident name _ _)) _ _ _ _) _ _ _) = name

instance GetCName CHMFunDef where
  getCName (CHMFunDef _ cFunDef _) = getCName cFunDef

instance GetCName CHMStructDef where
  getCName (CHMStructDef _ cStructUnion _) = getCName cStructUnion

instance GetCName CStructUnion where
  getCName (CStruct _ (Just (Ident name _ _)) _ _ _) = name

instance GetCName CExtDecl where
  getCName (CHMFDefExt chmFunDef) = getCName chmFunDef
  getCName (CHMSDefExt chmStructDef) = getCName chmStructDef
  getCName (CFDefExt cFunDef)     = getCName cFunDef
  getCName (CDeclExt cFunDecl)    = getCName cFunDecl

instance GetCName CDecl where
  getCName (CDecl _ [(Just (CDeclr (Just (Ident name _ _)) (CFunDeclr{} : _) _ _ _), Nothing, Nothing)] _) = name

class GetCName a => GetSU a where
  getSUName :: a -> Id
  getSUType :: a -> CStructTag
  getSUName = getCName

instance GetSU CExtDecl where
  getSUType (CHMSDefExt chmStructDef) = getSUType chmStructDef

instance GetSU CHMStructDef where
  getSUType (CHMStructDef _ cStructUnion _) = getSUType cStructUnion

instance GetSU CStructUnion where
  getSUType (CStruct tag _ _ _ _) = tag
