{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module CHM.TransformMonad
  ( MethodNamed
  , Method(..)
  , TransformMonad(..)
  , GetCName(..)
  , GetSU(..)
  , TypeDepth (..)
  , TState
  , PosData(..)
  , initTransformMonad
  , niceError
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
  , sizeofFunc
  , alignofFunc
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

import qualified Data.ByteString.Char8 as T

import TypingHaskellInHaskell

import Language.C.Data
import Language.C.Syntax
import Language.C.Data.Ident (Ident(..))
import Language.C.Data.Error (mkErrorInfo)

-- | Abstraction of a local variable 'Scope'
data Scope = Scope
  { scopeName :: Id
  , scopeId :: Int
  , scopeVars :: Set.Set Id
  } deriving(Show)

-- | Used to represent return expressions of functions
type ReturnExpr = Expr

-- | Initialize a new 'Scope'
initScope :: Id -> Int -> Scope
initScope name id = Scope
  { scopeName = name
  , scopeId = id
  , scopeVars = mempty
  }

-- | Initialize a new 'Scope'
initGlobalScope :: Scope
initGlobalScope = Scope
  { scopeName = T.pack "global"
  , scopeId = 0
  , scopeVars = mempty
  }

-- | Remembers the method's 'Scheme' and a set of 'Type's of its instances
data Method = Method
  { methodScheme :: Scheme
  , methodInstances :: Set.Set Type
  } deriving(Show)

-- | Initializes a new 'Method'
initMethod :: Scheme -> Method
initMethod s = Method
  { methodScheme = s
  , methodInstances = mempty
  }

{- |
  Stores the kind and the position of a defined struct,
  kinds tell us how many type variables they take,
  position is stored for checking duplications and for
  debugging purposes
-}
data Struct = Struct
  { structKind :: Kind
  , structPos :: NodeInfo
  } deriving(Show)

-- | Stores data for user-defined classes
newtype UserClass = UserClass
  { methods :: Map.Map Id Method
    -- ^ A Map of all methods in a class
  } deriving(Show)

newtype PosData =
  PosAnonData Int

-- | Used mainly in lists of 'Method's
type MethodNamed = (Id, Method)

-- | Returns a list of 'Method's of the given 'UserClass'
getClassMethods :: UserClass -> [MethodNamed]
getClassMethods = Map.toList . methods

-- | Initializes a new 'UserClass'
initUserClass :: UserClass
initUserClass = UserClass
  { methods = mempty
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
  , posData :: Map.Map NodeInfo PosData
    -- ^ things to remember about some locations
  , memberClasses :: EnvTransformer
    -- ^ all classes and their instances
  , builtIns :: Map.Map Id Scheme
    -- ^ all created symbols
  }

-- | Monad that holds the side effects of parsing the AST
type TState = State TransformMonad

-- | Common type constants

niceError :: String -> NodeInfo -> String
niceError =
  (show .) . mkErrorInfo LevelError

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
  castFunc, sizeofFunc, alignofFunc, cNULL :: Id

{-
  Operators follow a naming convention where there is
  the operator itself followed by the number of its operands
  (with notable exception where we have to distinguish the
  pre-increment and post-increment operators)

  This naming convention ensures the names are simple enough
  and that they resemble their appearance in the code while
  giving unique names to their unary and binary counterparts
-}

mulOpFunc     = T.pack "*2"
divOpFunc     = T.pack "/2"
modOpFunc     = T.pack "%2"
addOpFunc     = T.pack "+2"
subOpFunc     = T.pack "-2"
shlOpFunc     = T.pack "<<2"  -- TODO: <<2 unimplemented
shrOpFunc     = T.pack ">>2"  -- TODO: >>2 unimplemented
xorOpFunc     = T.pack "^2"  -- TODO: ^2 unimplemented
orOpFunc      = T.pack "|2"  -- TODO: |2 unimplemented
andOpFunc     = T.pack "&2"  -- TODO: &2 unimplemented
logAndOpFunc  = T.pack "&&2"  -- TODO: &&2 unimplemented
logOrOpFunc   = T.pack "||2"  -- TODO: ||2 unimplemented

eqOpFunc      = T.pack "==2"
neqOpFunc     = T.pack "!=2"
ltOpFunc      = T.pack "<2"
gtOpFunc      = T.pack ">2"
leOpFunc      = T.pack "<=2"
geOpFunc      = T.pack ">=2"

assOpFunc     = T.pack "=2"
mulAssOpFunc  = T.pack "*=2"
divAssOpFunc  = T.pack "/=2"
modAssOpFunc  = T.pack "%=2"
addAssOpFunc  = T.pack "+=2"
subAssOpFunc  = T.pack "-=2"
shlAssOpFunc  = T.pack "<<=2"  -- TODO: <<= unimplemented
shrAssOpFunc  = T.pack ">>=2"  -- TODO: >>= unimplemented
andAssOpFunc  = T.pack "&=2"  -- TODO: &= unimplemented
xorAssOpFunc  = T.pack "^=2"  -- TODO: ^= unimplemented
orAssOpFunc   = T.pack "|=2"  -- TODO: |= unimplemented

preIncOpFunc  = T.pack "++1"
postIncOpFunc = T.pack "1++"
preDecOpFunc  = T.pack "--1"
postDecOpFunc = T.pack "1--"
plusOpFunc    = T.pack "+1"
minusOpFunc   = T.pack "-1"
complOpFunc   = T.pack "~1"
negOpFunc     = T.pack "!1"

commaOpFunc   = T.pack ",2"
ternaryOpFunc = T.pack "?:3"
elvisOpFunc   = T.pack "?:2"
indexOpFunc   = T.pack "[]2"
refFunc       = T.pack "&1"
derefFunc     = T.pack "*1"

returnFunc    = T.pack "@return"
caseFunc      = T.pack "@case"
castFunc      = T.pack "@cast"
sizeofFunc      = T.pack "@sizeof"
alignofFunc      = T.pack "@alignof"

cNULL      = T.pack "NULL"

-- | Initializes the transform monad's state
initTransformMonad :: TransformMonad
initTransformMonad =
  let
    aVar = Tyvar (T.pack "a") Star
    bVar = Tyvar (T.pack "b") Star
    aTVar = TVar aVar
    bTVar = TVar bVar
  in TransformMonad
    { tuples = mempty
    , createdClasses = mempty
    , nested = [initGlobalScope]
    , lastScope = 0
    , registeredStructs = mempty
    , switchScopes = []
    , functionScopes = []
    , anonymousCounter = 0
    , userClasses = mempty
    , typeVariables = [[]]
    , typeAliases = [mempty]
    , variableClasses = [[]]
    , posData = mempty
    , memberClasses =
      -- TODO: the "real" implementation would need a lot more comprehensive list
      -- all built-in classe:
      addClass (T.pack "Num") []
      <:> addClass (T.pack "Add") []
      <:> addClass (T.pack "Sub") []
      <:> addClass (T.pack "Mul") []
      <:> addClass (T.pack "Div") []
      <:> addClass (T.pack "Mod") []
      <:> addClass (T.pack "Eq") []
      <:> addClass (T.pack "Eq0") []  -- TODO, for zero-comparable types (used in control statement conditions)
      <:> addClass (T.pack "LG") []
      <:> addClass (T.pack "BinOp") []
      <:> addClass (T.pack "LogOp") []
      -- all built-in instances (work in -- TODO)
      <:> addInst [] (IsIn (T.pack "Num") tInt)
      <:> addInst [] (IsIn (T.pack "Num") tShort)
      <:> addInst [] (IsIn (T.pack "Num") tLong)
      <:> addInst [] (IsIn (T.pack "Num") tChar)
      <:> addInst [] (IsIn (T.pack "Add") tInt)
      <:> addInst [] (IsIn (T.pack "Add") tChar)
      <:> addInst [] (IsIn (T.pack "Add") tFloat)
      <:> addInst [] (IsIn (T.pack "Add") tDouble)
      <:> addInst [] (IsIn (T.pack "Add") (pointer aTVar))
      <:> addInst [] (IsIn (T.pack "Sub") tInt)
      <:> addInst [] (IsIn (T.pack "Sub") tChar)
      <:> addInst [] (IsIn (T.pack "Sub") tFloat)
      <:> addInst [] (IsIn (T.pack "Sub") tDouble)
      <:> addInst [] (IsIn (T.pack "Sub") (pointer aTVar))
      <:> addInst [] (IsIn (T.pack "Mul") tInt)
      <:> addInst [] (IsIn (T.pack "Mul") tFloat)
      <:> addInst [] (IsIn (T.pack "Mul") tDouble)
      <:> addInst [] (IsIn (T.pack "Div") tInt)
      <:> addInst [] (IsIn (T.pack "Div") tFloat)
      <:> addInst [] (IsIn (T.pack "Div") tDouble)
      <:> addInst [] (IsIn (T.pack "Mod") tInt)
      <:> addInst [] (IsIn (T.pack "Eq")  tInt)
      <:> addInst [] (IsIn (T.pack "Eq")  tChar)
      <:> addInst [] (IsIn (T.pack "Eq")  tFloat)
      <:> addInst [] (IsIn (T.pack "Eq")  tDouble)
      <:> addInst [] (IsIn (T.pack "Eq")  (pointer aTVar))
      <:> addInst [] (IsIn (T.pack "Eq0")  tInt)
      <:> addInst [] (IsIn (T.pack "Eq0")  tChar)
      <:> addInst [] (IsIn (T.pack "Eq0")  tFloat)
      <:> addInst [] (IsIn (T.pack "Eq0")  tDouble)
      <:> addInst [] (IsIn (T.pack "Eq0")  (pointer aTVar))
      <:> addInst [] (IsIn (T.pack "LG")  tInt)
      <:> addInst [] (IsIn (T.pack "LG")  tChar)
      <:> addInst [] (IsIn (T.pack "LG")  tFloat)
      <:> addInst [] (IsIn (T.pack "LG")  tDouble)
      <:> addInst [] (IsIn (T.pack "LG")  (pointer aTVar))
      <:> addInst [] (IsIn (T.pack "BinOp")  tInt)
      <:> addInst [] (IsIn (T.pack "BinOp")  tBool)
      <:> addInst [] (IsIn (T.pack "BinOp")  tChar)
    , builtIns =
      let
        aSFuncWithClasses cs = quantify (Set.fromList [aVar]) (cs :=> (aTVar `fn` tSize_t))
        -- | functions of the type 'a -> a'
        aaFuncWithClasses cs = quantify (Set.fromList [aVar]) (cs :=> (aTVar `fn` aTVar))
        -- | functions of the type 'a -> a -> a'
        aaaFuncWithClasses cs = quantify (Set.fromList [aVar]) (cs :=> (aTVar `fn` aTVar `fn` aTVar))
        -- | functions of the type '(a, a) -> a'
        t2aaaFuncWithClasses cs = quantify (Set.fromList [aVar]) (cs :=> (tupleTypes [aTVar, aTVar] `fn` aTVar))
        -- | functions of the type 'a -> a -> Void'
        aaVFuncWithClasses cs = quantify (Set.fromList [aVar]) (cs :=> (aTVar `fn` aTVar `fn` tVoid))
        -- | functions of the type '(a, a) -> Void'
        t2aaVFuncWithClasses cs = quantify (Set.fromList [aVar]) (cs :=> (tupleTypes [aTVar, aTVar] `fn` tVoid))
        -- | functions of the type 'a -> b -> a'
        abaFuncWithClasses cs = quantify (Set.fromList [aVar, bVar]) (cs :=> (aTVar `fn` bTVar `fn` aTVar))
        -- | functions of the type '(a, b) -> a'
        t2abaFuncWithClasses cs = quantify (Set.fromList [aVar, bVar]) (cs :=> (tupleTypes [aTVar, bTVar] `fn` aTVar))
        -- | functions of the type 'a -> b -> Bool'
        aaBFuncWithClasses cs = quantify (Set.fromList [aVar, bVar]) (cs :=> (aTVar `fn` aTVar `fn` tBool))
        -- | functions of the type '(a, b) -> Bool'
        t2abBFuncWithClasses cs = quantify (Set.fromList [aVar, bVar]) (cs :=> (tupleTypes [aTVar, bTVar] `fn` tBool))
      in Map.fromList . map (\(id:>:sc) -> (id, sc)) $
        [ cNULL :>: toScheme (tPointer `TAp` tNULL)
        , addOpFunc :>: aaaFuncWithClasses [IsIn (T.pack "Add") aTVar]
        , subOpFunc :>: aaaFuncWithClasses [IsIn (T.pack "Sub") aTVar]
        , mulOpFunc :>: aaaFuncWithClasses [IsIn (T.pack "Mul") aTVar]
        , divOpFunc :>: aaaFuncWithClasses [IsIn (T.pack "Div") aTVar]
        , modOpFunc :>: aaaFuncWithClasses [IsIn (T.pack "Mod") aTVar]
        , assOpFunc :>: aaaFuncWithClasses []
        , addAssOpFunc :>: aaaFuncWithClasses [IsIn (T.pack "Add") aTVar]
        , subAssOpFunc :>: aaaFuncWithClasses [IsIn (T.pack "Sub") aTVar]
        , mulAssOpFunc :>: aaaFuncWithClasses [IsIn (T.pack "Mul") aTVar]
        , divAssOpFunc :>: aaaFuncWithClasses [IsIn (T.pack "Div") aTVar]
        , modAssOpFunc :>: aaaFuncWithClasses [IsIn (T.pack "Mod") aTVar]
        -- , shlAssOpFunc :>:
        -- , shrAssOpFunc :>:
        , andAssOpFunc :>: aaFuncWithClasses [IsIn (T.pack "BinOp") aTVar]
        , xorAssOpFunc :>: aaFuncWithClasses [IsIn (T.pack "BinOp") aTVar]
        , orAssOpFunc :>: aaFuncWithClasses [IsIn (T.pack "BinOp") aTVar]
        , eqOpFunc :>: aaBFuncWithClasses [IsIn (T.pack "Eq") aTVar]
        , neqOpFunc :>: aaBFuncWithClasses [IsIn (T.pack "Eq") aTVar]
        , ltOpFunc :>: aaBFuncWithClasses [IsIn (T.pack "LG") aTVar]
        , gtOpFunc :>: aaBFuncWithClasses [IsIn (T.pack "LG") aTVar]
        , leOpFunc :>: aaBFuncWithClasses [IsIn (T.pack "LG") aTVar, IsIn (T.pack "Eq") aTVar]
        , geOpFunc :>: aaBFuncWithClasses [IsIn (T.pack "LG") aTVar, IsIn (T.pack "Eq") aTVar]
        , preIncOpFunc  :>: aaFuncWithClasses [IsIn (T.pack "Num") aTVar, IsIn (T.pack "Add") aTVar]
        , postIncOpFunc :>: aaFuncWithClasses [IsIn (T.pack "Num") aTVar, IsIn (T.pack "Add") aTVar]
        , preDecOpFunc  :>: aaFuncWithClasses [IsIn (T.pack "Num") aTVar, IsIn (T.pack "Sub") aTVar]
        , postDecOpFunc :>: aaFuncWithClasses [IsIn (T.pack "Num") aTVar, IsIn (T.pack "Sub") aTVar]
        , plusOpFunc    :>: aaFuncWithClasses [IsIn (T.pack "Add") aTVar]
        , minusOpFunc   :>: aaFuncWithClasses [IsIn (T.pack "Sub") aTVar]
        , complOpFunc   :>: aaFuncWithClasses [IsIn (T.pack "BinOp") aTVar]
        , negOpFunc     :>: toScheme (tBool `fn` tBool)
        , commaOpFunc :>: quantify (Set.fromList [aVar, bVar]) ([] :=> (aTVar `fn` bTVar `fn` bTVar))
        , ternaryOpFunc :>: quantify (Set.fromList [aVar, bVar]) ([] :=> (aTVar `fn` bTVar `fn` bTVar `fn` bTVar)) -- TODO: aTVar has to be zero-comparable
        , elvisOpFunc :>: quantify (Set.fromList [aVar, bVar]) ([] :=> (aTVar `fn` bTVar `fn` bTVar)) -- TODO: aTVar has to be zero-comparable
        , indexOpFunc :>: quantify (Set.fromList [aVar, bVar]) ([] :=> (pointer aTVar `fn` bTVar `fn` aTVar)) -- TODO: bTVar has to be integral
        , refFunc :>: quantify (Set.fromList [aVar]) ([] :=> (aTVar `fn` pointer aTVar))
        , derefFunc :>: quantify (Set.fromList [aVar]) ([] :=> (pointer aTVar `fn` aTVar))
        , returnFunc :>: aaaFuncWithClasses []
        , caseFunc :>: quantify (Set.fromList [aVar]) ([] :=> (aTVar `fn` aTVar `fn` tBool))
        , castFunc :>: abaFuncWithClasses []
        , sizeofFunc :>: aSFuncWithClasses []
        , alignofFunc :>: aSFuncWithClasses []
        ]
    }

-- | Renames a variable's name depending on which scope we are currently parsing
renameScoped :: Scope -> Id -> Id
renameScoped Scope{scopeName = name, scopeId = n} id =
  if n == 0
    then id
    else T.concat [name, T.pack (show n <> ":"), id]

-- | Gets the name of the current switch statement
getSwitchName :: TState Id
getSwitchName = do
  TransformMonad{switchScopes = sScopes} <- get
  return . T.pack $ "@Switch" <> (show . head) sScopes

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
    _ -> return $ T.pack "@Error:" <> id

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
appendNextAnon id = (id <>) . T.pack . (':' :) . show <$> getNextAnon

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
    , typeAliases = mempty : tAs
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

filterTypes :: Type -> (Set.Set Tyvar, Set.Set Id) -> (Set.Set Tyvar, Set.Set Id)
filterTypes t accumulator@(tSet, idSet)
  | idSet == mempty = accumulator
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
      in filterClasses (tVars', preds'', preds' <> outPreds)

-- | Replaces aliases created in the last chm head by real type variables
replaceAliases :: Type -> TState Type
replaceAliases t = do
  tAs <- gets typeAliases
  return $ applyAliases' (Map.unions tAs) t

applyAliases' :: Map.Map Id Type -> Type -> Type
applyAliases' tAs t@(TVar (Tyvar id _)) =
  maybe t (applyAliases' tAs) (id `Map.lookup` tAs)
applyAliases' tAs (TAp t1 t2) = TAp (applyAliases' tAs t1) (applyAliases' tAs t2)
applyAliases' _ t = t

-- | Replaces type annotations with generic types and constraints (see 'quantify')
chmScheme :: Type -> TState Scheme
chmScheme t = do
  state@TransformMonad
    { typeVariables = tVs
    , variableClasses = vCs
    } <- get
  t' <- replaceAliases t
  let
    tVars = Set.fromList [id | Tyvar id _ <- concat tVs]
    (types, _) = filterTypes t' (mempty, tVars)
    (types', _, classes) = filterClasses (types, concat vCs, [])
  return $ quantify types' $ classes :=> t'
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
          (if T.null id
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
  enterScope mempty
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
        ('(' `T.cons` T.replicate (n - 1) ',' <> (')' `T.cons` T.pack (show n)))
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
getTupleCon n = Forall (replicate n Star) $ [] :=> tupleize (map TGen [0 .. n-1])

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
      , builtIns = Map.insert translate (getTupleCon n) bIs
      }
    return translate
  where translate = T.pack $ "@make_tuple" <> show n

-- | Creates a new name for the type class of the getter/setter of the member field
memberClassName :: Id -> Id
memberClassName = T.append (T.pack "Has_")

-- | This has to be named so that it cannot collide with
-- other user-defined functions
memberGetterName :: Id -> Id
memberGetterName = T.append (T.pack ".get:")

{- |
  Returns id of the given member's getter
-}
getMember :: Ident -> TState Id
getMember id@(Ident sId _ _) = return . memberGetterName $ T.pack sId

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
    sVar = Tyvar (T.pack "structVar") Star
    sTVar = TVar sVar
    mClassName = memberClassName mId
    sCon = TCon (Tycon sId Star)
    getterId = memberGetterName mId
    getterScheme =
      quantify
        (Set.singleton sVar)
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
      , builtIns = Map.insert getterId getterScheme bIs
      , createdClasses = mId `Set.insert` cs
      }

-- | creates a getter/setter for a given member field of a struct with a specified type
registerCHMMember :: Id -> Id -> Type -> TState ()
registerCHMMember sId mId t = do
  t' <- replaceAliases t
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
    sVar = Tyvar (T.pack "structVar") sKind
    sTVar = foldl TAp (TVar sVar) tVars
    sCon = foldl TAp (TCon (Tycon sId sKind)) tVars
    getterId = memberGetterName mId
    getterScheme =
      quantify
        (Set.fromList (sVar : head tVs))
        ((IsIn mClassName sTVar : head vCs) :=> (sTVar `fn` t'))
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
      , builtIns = Map.insert getterId getterScheme bIs
      , createdClasses = mId `Set.insert` cs
      }

-- | Creates a tuple of parameter types if there is a multiple of them,
-- if there is only one, returns it without creating a tuple
createParamsType :: [Type] -> Type
createParamsType [t] = t
createParamsType ts = foldl TAp (getTupleOp $ length ts) ts

-- | Makes a new entry for the given struct in the 'TransformMonad'
registerStruct :: Id -> NodeInfo -> TState Bool
registerStruct id nInfo = do
  state@TransformMonad{registeredStructs = rSs, typeVariables = tVs} <- get
  case id `Map.lookup` rSs of
    Just struct@Struct{structPos = sInfo} ->
      if sInfo == nInfo
        then return False
        else error $
          niceError "struct redefinition" nInfo <>
          ('\n' : niceError "\tpreviously defined here" sInfo)
    Nothing -> do
      put state
        { registeredStructs =
            Map.insert
              id
              Struct
                { structKind =
                    if null tVs
                      then Star
                      else takeNKind (length $ head tVs)
                , structPos = nInfo
                }
              rSs
        }
      return True

-- | returns the kind of a struct
getStructKind :: Id -> TState (Maybe Kind)
getStructKind id = do
  structs <- gets registeredStructs
  return $ structKind <$> (id `Map.lookup` structs)

-- | Makes a new entry in the class environment and in the 'TransformMonad'
registerClass :: Id -> Maybe Type ->  TState Bool
registerClass id mCType = do
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
      classType = case mCType of
        Nothing -> createParamsType $ TVar <$> tVars
        Just classType' -> classType'
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
  return . (id <>) . T.pack $ '_' : show num  -- TODO: better mangling is advised

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

instance GetCName CHMCDef where
  getCName (CHMCDef ident _ _ _) = getCName ident
  getCName (CHMCDefParams ident _ _ _ _) = getCName ident

instance GetCName CHMIDef where
  getCName (CHMIDef ident _ _ _) = getCName ident
  getCName (CHMIDefHead ident _ _ _ _) = getCName ident

instance GetCName CFunDef where
  getCName (CFunDef _ (CDeclr (Just ident) _ _ _ _) _ _ _) = getCName ident

instance GetCName CHMFunDef where
  getCName (CHMFunDef _ cFunDef _) = getCName cFunDef

instance GetCName CHMStructDef where
  getCName (CHMStructDef _ cStructUnion _) = getCName cStructUnion

instance GetCName CStructUnion where
  getCName (CStruct _ (Just ident) _ _ _) = getCName ident

instance GetCName CExtDecl where
  getCName (CHMCDefExt chmCDef) = getCName chmCDef
  getCName (CHMIDefExt chmIDef) = getCName chmIDef
  getCName (CHMFDefExt chmFunDef) = getCName chmFunDef
  getCName (CHMSDefExt chmStructDef) = getCName chmStructDef
  getCName (CFDefExt cFunDef)     = getCName cFunDef
  getCName (CDeclExt cFunDecl)    = getCName cFunDecl

instance GetCName CDecl where
  getCName (CDecl _ [(Just (CDeclr (Just ident) (CFunDeclr{} : _) _ _ _), Nothing, Nothing)] _) =
    getCName ident

instance GetCName Ident where
  getCName (Ident name _ _) = T.pack name

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

-- | Returns the depth of a type, depth is equal to the depth of the longest branch in the tree representation of the type.
class TypeDepth a where
  typeDepth :: a -> Int

instance TypeDepth Type where
  typeDepth (TAp t1 t2) =
    1 + max (typeDepth t1) (typeDepth t2)
  typeDepth _ = 1

instance TypeDepth Scheme where
  typeDepth (Forall [] (_ :=> t)) =
    typeDepth t
