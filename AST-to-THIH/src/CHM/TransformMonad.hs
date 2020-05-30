{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module CHM.TransformMonad
  ( MethodNamed
  , Method(..)
  , TransformMonad(..)
  , GetCName(..)
  , GetSU(..)
  , TypeComplexity (..)
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
  , castFunc
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

-- | Abstraction of a local variable 'Scope'
data Scope = Scope
  { scopeName :: Id
  , scopeId :: Int
  , scopeVars :: Set.Set Id
  }

type ReturnExpr = Expr

-- | Initialize a new 'Scope'
initScope :: Id -> Int -> Scope
initScope name id = Scope
  { scopeName = name
  , scopeId = id
  , scopeVars = Set.empty
  }

-- | Initialize a new 'Scope'
initGlobalScope :: Scope
initGlobalScope = Scope
  { scopeName = "global"
  , scopeId = 0
  , scopeVars = Set.empty
  }

-- | Remembers the method's 'Scheme' and a set of 'Type's of its instances
data Method = Method
  { methodScheme :: Scheme
  , methodInstances :: Set.Set Type
  }

-- | Initializes a new 'Method'
initMethod :: Scheme -> Method
initMethod s = Method
  { methodScheme = s
  , methodInstances = Set.empty
  }

newtype Struct = Struct
  { structKind :: Kind
  }

newtype UserClass = UserClass
  { methods :: Map.Map Id Method
  }

-- | Used mainly in lists of 'Method's
type MethodNamed = (Id, Method)

-- | Returns a list of 'Method's of the given 'UserClass'
getClassMethods :: UserClass -> [MethodNamed]
getClassMethods = Map.toList . methods

-- | Initializes a new 'UserClass'
initUserClass :: UserClass
initUserClass = UserClass
  { methods = Map.empty
  }

-- | Contains all side effects of parsing the C AST to its thih representation
data TransformMonad = TransformMonad
  { tuples :: Set.Set Int
    -- ^ memory of created tuple makers
  , nested :: [Scope]
    -- ^ to avoid name collisions
  , switchScopes :: [Int]
    {- ^
      Remembers the number of the scope of a switch statement
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

-- | Monad that holds the side effects of parsing the AST
type TState = State TransformMonad

-- | Common type constants
tPointer, tConst, tError, tTuple3, tNULL :: Type

tPointer = TCon (Tycon "@Pointer" (Kfun Star Star))
tConst = TCon (Tycon "@Const" (Kfun Star Star))
tError = TCon (Tycon "@Error" Star)
tTuple3 = TCon (Tycon "(,,)3" (Kfun Star (Kfun Star (Kfun Star Star))))
tNULL = TCon (Tycon "@NULL" Star)

-- pointer reference & dereference functions
-- | thih representation of the unary & operator
ref :: Expr -> Expr
-- | thih representation of the unary * operator
deref :: Expr -> Expr
-- | thih representation of the * in declarations
pointer :: Type -> Type

ref = Ap (Var refFunc)
deref = Ap (Var derefFunc)
pointer = TAp tPointer


class OperatorFunction a where
  -- | Return the 'Id' of a function which represents the given operator
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

{- |
  These functions represent various operators and other
  language features that act like operators (e.g. 'CReturn')
-}
mulOpFunc, divOpFunc, modOpFunc, addOpFunc, subOpFunc,
  shlOpFunc, shrOpFunc, xorOpFunc, orOpFunc, andOpFunc,
  logAndOpFunc, logOrOpFunc, eqOpFunc, neqOpFunc, ltOpFunc,
  gtOpFunc, leOpFunc, geOpFunc, assOpFunc, mulAssOpFunc,
  divAssOpFunc, modAssOpFunc, addAssOpFunc, subAssOpFunc,
  shlAssOpFunc, shrAssOpFunc, andAssOpFunc, xorAssOpFunc,
  orAssOpFunc, preIncOpFunc, postIncOpFunc, preDecOpFunc,
  postDecOpFunc, plusOpFunc, minusOpFunc, complOpFunc,
  negOpFunc, commaOpFunc, ternaryOpFunc, elvisOpFunc,
  indexOpFunc, refFunc, derefFunc, returnFunc, caseFunc,
  castFunc, cNULL :: Id

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

preIncOpFunc  = "++1"
postIncOpFunc = "1++"
preDecOpFunc  = "--1"
postDecOpFunc = "1--"
plusOpFunc    = "+1"
minusOpFunc   = "-1"
complOpFunc   = "~1"
negOpFunc     = "!1"

commaOpFunc   = ",2"
ternaryOpFunc = "?:3"
elvisOpFunc   = "?:2"
indexOpFunc   = "[]2"
refFunc       = "&1"
derefFunc     = "*1"

returnFunc    = "@return"
caseFunc      = "@case"

castFunc      = "@cast"
cNULL      = "NULL"

-- | Initializes the transform monad's state
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
    , nested = [initGlobalScope]
    , lastScope = 0
    , registeredStructs = Map.empty
    , switchScopes = []
    , functionScopes = []
    , anonymousCounter = 0
    , userClasses = Map.empty
    , typeVariables = [[]]
    , typeAliases = [Map.empty]
    , variableClasses = [[]]
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
      <:> addInst [] (IsIn "Add" tChar)
      <:> addInst [] (IsIn "Add" tFloat)
      <:> addInst [] (IsIn "Add" tDouble)
      <:> addInst [] (IsIn "Add" (pointer aTVar))
      <:> addInst [] (IsIn "Sub" tInt)
      <:> addInst [] (IsIn "Sub" tChar)
      <:> addInst [] (IsIn "Sub" tFloat)
      <:> addInst [] (IsIn "Sub" tDouble)
      <:> addInst [] (IsIn "Sub" (pointer aTVar))
      <:> addInst [] (IsIn "Mul" tInt)
      <:> addInst [] (IsIn "Mul" tFloat)
      <:> addInst [] (IsIn "Mul" tDouble)
      <:> addInst [] (IsIn "Div" tInt)
      <:> addInst [] (IsIn "Div" tFloat)
      <:> addInst [] (IsIn "Div" tDouble)
      <:> addInst [] (IsIn "Mod" (pair tInt tInt))
      <:> addInst [] (IsIn "Eq"  tInt)
      <:> addInst [] (IsIn "Eq"  tChar)
      <:> addInst [] (IsIn "Eq"  tFloat)
      <:> addInst [] (IsIn "Eq"  tDouble)
      <:> addInst [] (IsIn "Eq"  (pointer aTVar))
      <:> addInst [] (IsIn "LG"  tInt)
      <:> addInst [] (IsIn "LG"  tChar)
      <:> addInst [] (IsIn "LG"  tFloat)
      <:> addInst [] (IsIn "LG"  tDouble)
      <:> addInst [] (IsIn "LG"  (pointer aTVar))
      <:> addInst [] (IsIn "BinOp"  tInt)
      <:> addInst [] (IsIn "BinOp"  tBool)
      <:> addInst [] (IsIn "BinOp"  tChar)
    , builtIns =
      let
        -- functions of the type 'a -> a'
        aaFuncWithClasses cs = quantify [aVar] (cs :=> (aTVar `fn` aTVar))
        -- functions of the type 'a -> a -> a'
        aaaFuncWithClasses cs = quantify [aVar] (cs :=> (aTVar `fn` aTVar `fn` aTVar))
        -- functions of the type '(a, a) -> a'
        t2aaaFuncWithClasses cs = quantify [aVar] (cs :=> (tupleTypes [aTVar, aTVar] `fn` aTVar))
        -- functions of the type 'a -> a -> Void'
        aaVFuncWithClasses cs = quantify [aVar] (cs :=> (aTVar `fn` aTVar `fn` tVoid))
        -- functions of the type '(a, a) -> Void'
        t2aaVFuncWithClasses cs = quantify [aVar] (cs :=> (tupleTypes [aTVar, aTVar] `fn` tVoid))
        -- functions of the type 'a -> b -> a'
        abaFuncWithClasses cs = quantify [aVar, bVar] (cs :=> (aTVar `fn` bTVar `fn` aTVar))
        -- functions of the type '(a, b) -> a'
        t2abaFuncWithClasses cs = quantify [aVar, bVar] (cs :=> (tupleTypes [aTVar, bTVar] `fn` aTVar))
        -- functions of the type 'a -> b -> Bool'
        aaBFuncWithClasses cs = quantify [aVar, bVar] (cs :=> (aTVar `fn` aTVar `fn` tBool))
        -- functions of the type '(a, b) -> Bool'
        t2abBFuncWithClasses cs = quantify [aVar, bVar] (cs :=> (tupleTypes [aTVar, bTVar] `fn` tBool))
      in Set.fromList
        [ cNULL :>: toScheme (tPointer `TAp` tNULL)
        , addOpFunc :>: aaaFuncWithClasses [IsIn "Add" aTVar]
        , subOpFunc :>: aaaFuncWithClasses [IsIn "Sub" aTVar]
        , mulOpFunc :>: aaaFuncWithClasses [IsIn "Mul" aTVar]
        , divOpFunc :>: aaaFuncWithClasses [IsIn "Div" aTVar]
        , modOpFunc :>: aaaFuncWithClasses [IsIn "Mod" aTVar]
        , assOpFunc :>: aaaFuncWithClasses []
        , addAssOpFunc :>: aaaFuncWithClasses [IsIn "Add" aTVar]
        , subAssOpFunc :>: aaaFuncWithClasses [IsIn "Sub" aTVar]
        , mulAssOpFunc :>: aaaFuncWithClasses [IsIn "Mul" aTVar]
        , divAssOpFunc :>: aaaFuncWithClasses [IsIn "Div" aTVar]
        , modAssOpFunc :>: aaaFuncWithClasses [IsIn "Mod" aTVar]
        -- , shlAssOpFunc :>:
        -- , shrAssOpFunc :>:
        , andAssOpFunc :>: aaFuncWithClasses [IsIn "BinOp" aTVar]
        , xorAssOpFunc :>: aaFuncWithClasses [IsIn "BinOp" aTVar]
        , orAssOpFunc :>: aaFuncWithClasses [IsIn "BinOp" aTVar]
        , eqOpFunc :>: aaBFuncWithClasses [IsIn "Eq" aTVar]
        , neqOpFunc :>: aaBFuncWithClasses [IsIn "Eq" aTVar]
        , ltOpFunc :>: aaBFuncWithClasses [IsIn "LG" aTVar]
        , gtOpFunc :>: aaBFuncWithClasses [IsIn "LG" aTVar]
        , leOpFunc :>: aaBFuncWithClasses [IsIn "LG" aTVar, IsIn "Eq" aTVar]
        , geOpFunc :>: aaBFuncWithClasses [IsIn "LG" aTVar, IsIn "Eq" aTVar]
        , preIncOpFunc  :>: aaFuncWithClasses [IsIn "Num" aTVar, IsIn "Add" aTVar]
        , postIncOpFunc :>: aaFuncWithClasses [IsIn "Num" aTVar, IsIn "Add" aTVar]
        , preDecOpFunc  :>: aaFuncWithClasses [IsIn "Num" aTVar, IsIn "Sub" aTVar]
        , postDecOpFunc :>: aaFuncWithClasses [IsIn "Num" aTVar, IsIn "Sub" aTVar]
        , plusOpFunc    :>: aaFuncWithClasses [IsIn "Add" aTVar]
        , minusOpFunc   :>: aaFuncWithClasses [IsIn "Sub" aTVar]
        , complOpFunc   :>: aaFuncWithClasses [IsIn "BinOp" aTVar]
        , negOpFunc     :>: toScheme (tBool `fn` tBool)
        , commaOpFunc :>: quantify [aVar, bVar] ([] :=> (aTVar `fn` bTVar `fn` bTVar))
        , ternaryOpFunc :>: quantify [aVar, bVar] ([] :=> (aTVar `fn` bTVar `fn` bTVar `fn` bTVar)) -- TODO: aTVar has to be 0 comparable
        , elvisOpFunc :>: quantify [aVar, bVar] ([] :=> (aTVar `fn` bTVar `fn` bTVar)) -- TODO: aTVar has to be 0 comparable
        , indexOpFunc :>: quantify [aVar, bVar] ([] :=> (pointer aTVar `fn` bTVar `fn` aTVar)) -- TODO: bTVar has to be integral
        , refFunc :>: quantify [aVar] ([] :=> (aTVar `fn` pointer aTVar))
        , derefFunc :>: quantify [aVar] ([] :=> (pointer aTVar `fn` aTVar))
        , returnFunc :>: aaaFuncWithClasses []
        , caseFunc :>: quantify [aVar] ([] :=> (aTVar `fn` aTVar `fn` tBool))
        , castFunc :>: abaFuncWithClasses []
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

{- |
  Returns the 'Scope' that contains the closest match for the given
  symbol
-}
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

-- | Stores the symbol to the given 'Scope'
storeName :: Id -> TState ()
storeName id = do
  state@TransformMonad{nested = ns} <- get
  case ns of
    scope@Scope{scopeVars = names} : rest ->
      put state
        { nested = scope{scopeVars = id `Set.insert` names} : rest
        }

-- | Retrieves the unique form of the name of the symbol
scopedName :: Id -> TState Id
scopedName id = do
  scope <- findName id
  case scope of
    Just s -> return $ renameScoped s id
    _ -> return $ "@Error:" ++ id

-- | Stores the given name to the current scope and returns its qualified name
sgName :: Id -> TState Id
sgName id = storeName id >> scopedName id

-- | Counts numbers to help give unique names
getNextAnon :: TState Int
getNextAnon = do
  state@TransformMonad{anonymousCounter = i} <- get
  put state {anonymousCounter = i + 1}
  return i

-- | Appends next anon number to the given name, see 'getNextAnon'
appendNextAnon :: Id -> TState Id
appendNextAnon id = (id ++) . (':' :) . show <$> getNextAnon

-- | Pushes the scopes of type variables (and aliases) and their classes
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

-- | adds the given type variable to the current chmHead scope
chmAddVariable :: Tyvar -> TState ()
chmAddVariable tyvar = do
  state@TransformMonad{typeVariables = tVs} <- get
  case tVs of
    ts:rest -> put state{typeVariables = (tyvar : ts) : rest}
    _ -> return . error $ "not in chm head block"

-- | adds the given type alias to the current chmHead scope
chmAddAlias :: Id -> Type -> TState ()
chmAddAlias id t = do
  state@TransformMonad{typeAliases = tAs} <- get
  case tAs of
    tas:restA -> put state
      { typeAliases = Map.insert id t tas : restA
      }
    _ -> return . error $ "not in chm head block"

-- | adds the given class predicate to the current chmHead scope
chmAddClass :: Pred -> TState ()
chmAddClass p = do
  state@TransformMonad{variableClasses = cs} <- get
  case cs of
    c:rest -> put state{variableClasses = (p : c) : rest}
    _ -> return . error $ "not in chm head block"

-- | Pulls all scopes of type variables (and aliases) and their classes
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
tupleTypes :: [Type] -> Type
tupleTypes ts = foldl TAp (getTupleOp . length $ ts) ts

-- | Returns a function that takes the specified 'Type's
-- and returns a tuple of them (see 'tupleTypes')
tupleize :: [Type] -> Type
tupleize ts = foldr fn (tupleTypes ts) ts

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

{- |
  Returns id of the given member's getter
-}
getMember :: Ident -> TState Id
getMember id@(Ident sId _ _) = return $ memberGetterName sId

{- |
  Registers a member getter for the given struct and its member
  expressed via their ids respectively,
  creates the member's getter class if it doesn't exist
-}
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
  return $ methodScheme <$> (Map.lookup mId . methods =<< Map.lookup cId uCs)

mangleName :: Id -> Type -> TState Id
mangleName id mType = do
  num <- getNextAnon
  return $ id ++ '_' : show num  -- TODO

{- |
  Adds a new instance of a method of the given class
  using the given name and the given type (in this order)
-}
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

-- | Supplies the initial state to a 'runState' call
runTState :: TState a -> (a, TransformMonad)
runTState a = runState a initTransformMonad

-- | Returns the name of the given C construct
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

-- | gets data from 'CStructUnion's and derived types
class GetCName a => GetSU a where
  getSUName :: a -> Id
  getSUType :: a -> CStructTag
  getSUName = getCName

-- | Retrieves the encapsulated 'CStructUnion' object
instance GetSU CExtDecl where
  getSUType (CHMSDefExt chmStructDef) = getSUType chmStructDef

instance GetSU CHMStructDef where
  getSUType (CHMStructDef _ cStructUnion _) = getSUType cStructUnion

instance GetSU CStructUnion where
  getSUType (CStruct tag _ _ _ _) = tag


class TypeComplexity a where
  typeComplexity :: a -> Int

instance TypeComplexity Type where
  typeComplexity (TAp t1 t2) =
    1 + max (typeComplexity t1) (typeComplexity t2)
  typeComplexity _ = 1

instance TypeComplexity Scheme where
  typeComplexity (Forall [] ([] :=> t)) =
    typeComplexity t
