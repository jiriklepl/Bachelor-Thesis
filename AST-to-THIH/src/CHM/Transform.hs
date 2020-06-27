{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module CHM.Transform
  ( Transform (..)
  , TransformCHMFunDef (..)
  , TState
  , TransformMonad (..)
  , GetCName(..)
  , GetSU(..)
  , TypeComplexity (..)
  , tPointer
  , runInfer
  , initTransformMonad
  , createParamsType
  , transformCHMType
  , getTransformResult
  , enterCHMHead
  , leaveCHMHead
  , enterFunction
  , leaveFunction
  , getAliases
  , chmScheme
  , takeNKind
  , typeInfer
  , flattenProgram
  , storeName
  , niceError
  ) where

import Debug.Trace

import Control.Monad.State
import Control.Monad((>=>), when)
import qualified Data.Set as Set
import qualified Data.Map as Map
import Data.Maybe

import qualified Data.ByteString.Char8 as T

import TypingHaskellInHaskell hiding (modify)

import Language.C.Data
import Language.C.Data.Ident (Ident(..))
import Language.C.Syntax

import CHM.TransformMonad

{- |
  Takes a C construct, parses it (with side effects
  kept in 'TState'), and returns a thih 'Program'
-}
class Transform a where
  transform :: a -> TState Program
  transform_ :: a -> TState ()
  transform_ = (>> return ()) . transform

{- |
  Just transforms the C construct into its
-}
getTransformResult :: Transform a => a -> Program
getTransformResult = fst . runTState . transform

{- |
  Runs thih on the given thih 'Program' using environment
  consisting of 'builtIns' and 'memberClasses' retrieved from the state
  and the given 'Assump's
-}
typeInfer :: Map.Map Id Scheme -> Program -> TState (Map.Map Id Scheme)
typeInfer assumps program = do
  TransformMonad{builtIns = bIs, memberClasses = mCs}  <- get
  case mCs initialEnv of
    Nothing -> error "Environment corrupted"
    Just cEnv -> return $ tiProgram cEnv (bIs <> assumps) program

{- |
  Runs thih on the given C construct after transforming it
  (using new state)
-}
runInfer :: Transform a => a -> Map.Map Id Scheme
runInfer a =
  let
    (program, TransformMonad{memberClasses=mCs, builtIns=bIs}) =
      runTState . transform $ a
  in
    case mCs initialEnv of
      Nothing -> error "Environment is broken"
      Just env -> tiProgram env bIs program

-- | Takes a 'Program' and flattens it into a 'BindGroup'
flattenProgram :: Program -> BindGroup
flattenProgram ((expls, impls) : rest) =
  let
    (restExpls, restImpls) = flattenProgram rest
  in (expls <> restExpls, impls <> restImpls)
flattenProgram [] = ([],[])

{- |
  Just reverses expls, this is used because of the order of dependencies
  in declarations inside functions
-}
reverseExpls :: BindGroup -> BindGroup
reverseExpls (expls, impls) = (reverse expls, impls)

{- |
  TODO: I should describe this and also check its validity
-}
reassemble :: BindGroup -> TState BindGroup
reassemble bindGroup@([(name, scheme, [(pats, Let (expls, impls) returnValue)])], []) = case expls of
  (eName, eScheme, [([],expr)]) : rest -> do
    let
      eScheme' = case (scheme, eScheme) of
        (Forall [] ([] :=> t1), Forall [] ([] :=> t2)) ->
          Forall [] ([] :=> (t2 `fn` t1))
      transformPars [] = return []
      transformPars (PVar id : pats) = do
        others <- transformPars pats
        return $ Var id : others
      transformPars (PCon (constr :>: _) pats' : pats) = do
        others <- transformPars pats
        tuple <- Var <$> getTuple (length pats')
        constrPars <- transformPars pats'
        return $ foldl Ap tuple constrPars : others
      innerName = T.pack "@INNER_" <> eName
    bindGroup' <- reassemble ([(innerName, eScheme', [(PVar eName : pats, Let (rest, impls) returnValue)])], [])
    let ([(iName, iScheme, [iAlt])], []) = bindGroup'
    others <- transformPars pats
    return ([(name, scheme, [(pats, foldl Ap (LambdaScheme iScheme iAlt) (expr : others))])], [])
  [] -> case impls of
    [] -> return ([(name, scheme, [(pats, returnValue)])], [])
    _ -> return bindGroup
  _ -> return bindGroup

-- | This goes through the structure and replaces temporary types with generics
class CHMSchemize a where
  chmSchemize :: a -> TState a

instance CHMSchemize Scheme where
  chmSchemize (Forall [] ([] :=> t)) = chmScheme t

instance CHMSchemize BindGroup where
  chmSchemize (expls, impls) = do
      expls' <- chmSchemize expls
      return (expls', impls)

instance CHMSchemize a => CHMSchemize [a] where
  chmSchemize = traverse chmSchemize

instance CHMSchemize Expl where
  chmSchemize (name, scheme, alts) = do
    scheme' <- chmSchemize scheme
    return (name, scheme', alts)

-- | Makes sure the top-most type is tConst (adds it if it isn't)
toConst :: Type -> Type
toConst c@(TAp tConst a) = c
toConst c = TAp tConst c

-- | Translates '[CDeclSpec]' type annotation to the haskell-like 'Type'
translateDeclSpecs :: [CDeclSpec] -> TState Type  -- TODO: just temporary implementation, should use the State monad
translateDeclSpecs (decl:decls) = case decl of
  CTypeSpec (CVoidType _) -> return tVoid
  CTypeSpec (CCharType _) -> return tChar
  CTypeSpec (CShortType _) -> return tShort
  CTypeSpec (CIntType _) -> return tInt
  CTypeSpec (CLongType _) ->
    if null decls
      then return tLong
      else (tLongSpec `TAp`) <$> translateDeclSpecs decls
  CTypeSpec (CFloatType _) -> return tFloat
  CTypeSpec (CDoubleType _) -> return tDouble
  CTypeSpec (CSignedType _) -> return tSigned
  CTypeSpec (CUnsigType _) -> return tUnsig
  CTypeSpec (CBoolType _) -> return tBool
  CTypeSpec (CComplexType _) -> return tComplex
  CTypeSpec (CInt128Type _) -> return tInt128
  CTypeSpec (CSUType (CStruct _ (Just ident) Nothing _ _) nInfo) -> do
    let name = getCName ident
    mKind <- getStructKind name
    case mKind of
      Just kind -> return $ TCon (Tycon name kind)
      Nothing -> return $ TCon (Tycon name Star)
{-
  On the above line `Star` is just a placeholder `Kind`, no `Kind` is
  actually known yet, but this should happen only in contexts of
  C declarations.

  The following would make pure declaration not work:
      Nothing -> error $ niceError
        ("cannot find the requested struct `" <> T.unpack name <> "`")
        nInfo
-}
  CTypeSpec (CSUType (CStruct _ (Just ident) (Just cDecls) _ nInfo) _) -> do
    let name = getCName ident
    registered <- registerStruct name nInfo
    when registered $ registerStructMembers name cDecls
    return (TCon (Tycon name Star))
  CTypeSpec (CSUType (CStruct _ Nothing (Just cDecls) _ nInfo) _ ) -> do
    name <- appendNextAnon (T.pack "@Struct")
    registered <- registerStruct name nInfo
    when registered $ registerStructMembers name cDecls
    return (TCon (Tycon name Star))
  CTypeSpec (CSUType (CStruct _ Nothing _ _ _) _ ) -> return tError  -- TODO
  CTypeSpec (CTypeDef ident _) -> do
    let name = getCName ident
    name <- scopedName name
    return $ TVar (Tyvar name Star)
  -- TODO: from here
  CTypeQual (CConstQual _) -> toConst <$> translateDeclSpecs decls  -- works only with west const :(
  CTypeQual (CVolatQual _) -> translateDeclSpecs decls  -- TODO
  CTypeQual (CRestrQual _) -> translateDeclSpecs decls  -- TODO
  CTypeQual (CAtomicQual _) -> translateDeclSpecs decls  -- TODO
  CTypeQual (CAttrQual _) -> translateDeclSpecs decls  -- TODO
  CTypeQual (CNullableQual _) -> translateDeclSpecs decls  -- TODO
  CTypeQual (CNonnullQual _) -> translateDeclSpecs decls  -- TODO
  CTypeQual (CClRdOnlyQual _) -> translateDeclSpecs decls  -- TODO
  CTypeQual (CClWrOnlyQual _) -> translateDeclSpecs decls  -- TODO
  CFunSpec _ -> translateDeclSpecs decls
  CStorageSpec _ -> translateDeclSpecs decls
  CAlignSpec _ -> translateDeclSpecs decls
  anon@CHMAnonType{} -> TVar . flip Tyvar Star <$> mangleAnonType anon

translateDerivedDecl :: Type -> [CDerivedDeclr] -> TState Type
translateDerivedDecl t [] = return t
translateDerivedDecl t (dDecl:dDecls) = do
  let
    translateQuals s (typeQual:tDecls) = case typeQual of
      (CConstQual _) -> toConst $ translateQuals s tDecls
      (CVolatQual _) -> translateQuals s tDecls  -- TODO
      (CRestrQual _) -> translateQuals s tDecls  -- TODO
      (CAtomicQual _) -> translateQuals s tDecls  -- TODO
      (CAttrQual _) -> translateQuals s tDecls  -- TODO
      (CNullableQual _) -> translateQuals s tDecls  -- TODO
      (CNonnullQual _) -> translateQuals s tDecls  -- TODO
      (CClRdOnlyQual _) -> translateQuals s tDecls  -- TODO
      (CClWrOnlyQual _) -> translateQuals s tDecls  -- TODO
    translateQuals s [] = s
    extractDecls (CDecl declSpecs [] _) = (declSpecs, [])
    extractDecls (CDecl declSpecs [(Nothing, _, _)] _) = (declSpecs, [])
    extractDecls (CDecl declSpecs [(Just (CDeclr _ derived _ _ _), _, _)] _) =
      (declSpecs, derived)
  t' <- translateDerivedDecl t dDecls
  case dDecl of
    CPtrDeclr typeQuals _ -> return $ translateQuals (pointer t') typeQuals
    CArrDeclr typeQuals _ _ -> return $ translateQuals (pointer t') typeQuals  -- TODO: this is just temporary
    -- old-style functions
    CFunDeclr (Left _) _ _ -> return tError  -- TODO
    -- new-style functions (non-variadic)
    CFunDeclr (Right (rawDecls, False)) _ _ -> do
      types <- sequenceA
        [ translateDeclSpecs specs >>= flip translateDerivedDecl derived
        | (specs, derived) <- extractDecls <$> rawDecls
        ]
      return $ foldl TAp (getTupleOp $ length types) types `fn` t'
    -- new-style functions (variadic)
    CFunDeclr (Right (decls, True)) _ _ -> return tError  -- TODO

translateDecl :: CDecl -> TState Type
translateDecl (CDecl declSpecs [] _) = translateDeclSpecs declSpecs
translateDecl (CDecl declSpecs [(Just (CDeclr _ cDerivedDeclrs _ _ _), Nothing, Nothing)] _) =
  translateDeclSpecs declSpecs >>= flip translateDerivedDecl cDerivedDeclrs

extractParameters :: [CDecl] -> TState Program
extractParameters (decl:decls) = case decl of
    CDecl declSpecs [] _ ->
      extractParameters decls
    CDecl declSpecs [(Nothing, _, _)] _ ->
      extractParameters decls
    CDecl declSpecs [(Just (CDeclr Nothing derived _ _ _), _, _)] _ ->
      extractParameters decls
    CDecl declSpecs [(Just (CDeclr (Just ident) derived _ _ _), _, _)] _ -> do
      let sId = getCName ident
      name <- sgName sId
      others <- extractParameters decls
      pureType <- translateDeclSpecs declSpecs
      expandedType <- translateDerivedDecl pureType derived
      return $ ([(name, toScheme expandedType, [])], []) : others
extractParameters [] = return []

registerStructMembers :: Id -> [CDecl] -> TState ()
registerStructMembers =
  registerStructMembersCommon registerMember

registerCHMStructMembers :: Id -> [CDecl] -> TState ()
registerCHMStructMembers =
  registerStructMembersCommon registerCHMMember

registerStructMembersCommon :: (Id -> Id -> Type -> TState()) -> Id -> [CDecl] -> TState ()
registerStructMembersCommon _ _ [] = return ()
registerStructMembersCommon registerMemberSpecial id cDecls = do
  let
    registerSingleCDecl (CDecl specs declrs a) =
      case declrs of
        (Just (CDeclr (Just ident) derivedDecls _ _ _), Nothing, Nothing):rest -> do
          let mId = getCName ident
          pureType <- translateDeclSpecs specs
          type' <- translateDerivedDecl pureType derivedDecls
          registerMemberSpecial id mId type'
          registerSingleCDecl (CDecl specs rest a)
        (Just (CDeclr (Just ident) derivedDecls _ _ _), Just _, Nothing):rest -> do
          let mId = getCName ident
          registerSingleCDecl (CDecl specs rest a)  -- TODO: this is probably error (but still recognized by c++ as kosher)
        [] -> return ()
  sequence_ (registerSingleCDecl <$> cDecls)

instance Transform a => Transform [a] where
  transform as = concat <$> traverse transform as

instance Transform Expl where
  transform expl = return [([expl],[])]

instance Transform Impl where
  transform impl = return [([],[[impl]])]

instance Transform CTranslUnit where
  transform (CTranslUnit [] _) = return []
  transform (CTranslUnit extDecls a) = transform extDecls

instance Transform CExtDecl where
  transform  (CDeclExt a)   = transform a
  transform  (CFDefExt a)   = transform a
  transform  (CHMFDefExt a) = transform a
  transform  (CHMSDefExt a) = transform a
  transform  (CHMCDefExt a) = transform a
  transform  (CHMIDefExt a) = transform a
  transform  (CAsmExt  a _) = transform a

-- these are better than the equivalent 'foldl Ap' because of the stronger type safety
ap2 :: Expr -> Expr -> Expr -> Expr
ap3 :: Expr -> Expr -> Expr -> Expr -> Expr

ap2 f a b = foldl Ap f [a, b]
ap3 f a b c = foldl Ap f [a, b, c]

transformExpr :: CExpr -> TState Expr
transformExpr cExpr = let
  in case cExpr of
  -- exprs is guaranteed to have at least 2 elements
  CComma exprs _ -> do
    exprs' <- traverse transformExpr exprs
    return $ foldl1
      (Ap . Ap (Var commaOpFunc))
      exprs'
  CAssign op lExpr rExpr _ -> do
    lExpr' <- transformExpr lExpr
    rExpr' <- transformExpr rExpr
    return $ ap2
      (Var $ operatorFunction op)
      lExpr'
      rExpr'
  -- this is the ternary operator
  CCond cExpr (Just tExpr) fExpr _ -> do
    cExpr' <- transformExpr cExpr
    tExpr' <- transformExpr tExpr
    fExpr' <- transformExpr fExpr
    return $ ap3
      (Var ternaryOpFunc)
      cExpr'
      tExpr'
      fExpr'
  -- this is elvis (supported by gnu)
  CCond cExpr Nothing fExpr _ -> do
    cExpr' <- transformExpr cExpr
    fExpr' <- transformExpr fExpr
    return $ ap2
      (Var elvisOpFunc)
      cExpr'
      fExpr'
  CBinary op lExpr rExpr _ -> do
    lExpr' <- transformExpr lExpr
    rExpr' <- transformExpr rExpr
    return $ Var (operatorFunction op) `Ap` lExpr' `Ap` rExpr'
  CCast cDecl tExpr _ -> do
    cDecl' <- translateDecl cDecl
    tExpr' <- transformExpr tExpr
    anonName <- appendNextAnon (T.pack "@Cast")
    return $ ap2
      (Var castFunc)
      (Const (anonName :>: toScheme cDecl'))
      tExpr'
  CUnary op expr _ -> do
    expr' <- transformExpr expr
    return $ Ap
      (Var $ operatorFunction op)
      expr'
  CSizeofExpr sExpr _ -> do
    sExpr' <- transformExpr sExpr
    return $ Var sizeofFunc `Ap` sExpr'
  CSizeofType sDecl _ -> do
    sDecl' <- translateDecl sDecl
    name <- appendNextAnon (T.pack "@Decl")
    return $ Var sizeofFunc `Ap` Const (name :>: toScheme sDecl')
  CAlignofExpr sExpr _ -> do
    sExpr' <- transformExpr sExpr
    return $ Var alignofFunc `Ap` sExpr'
  CAlignofType sDecl _ -> do
    sDecl' <- translateDecl sDecl
    name <- appendNextAnon (T.pack "@Decl")
    return $ Var alignofFunc `Ap` Const (name :>: toScheme sDecl')
  -- TODO: CComplexReal
  CIndex aExpr iExpr _ -> do
    aExpr' <- transformExpr aExpr
    iExpr' <- transformExpr iExpr
    return $ ap2
      (Var indexOpFunc)
      aExpr'
      iExpr'
  CCall func exprs _ -> do
    tuple <- getTuple (length exprs)
    func' <- transformExpr func
    exprs' <- traverse transformExpr exprs
    return $ Ap
      func'
      (foldl Ap (Var tuple) exprs')
  -- sExpr->mId
  CMember sExpr mId True _ -> do
    member <- getMember mId
    sExpr' <- transformExpr sExpr
    return $ Ap
      (Var member)
      (deref sExpr')
  -- sExpr.mId
  CMember sExpr mId False _ -> do
    member <- getMember mId
    sExpr' <- transformExpr sExpr
    return $ Ap
      (Var member)
      sExpr'
  CVar ident _ -> do
    let sId = getCName ident
    name <- scopedName sId
    return $ Var name
  -- CConst is literal
  -- TODO: check it
  CConst (CIntConst (CInteger i _ _) _) ->
    return $ Lit $ LitInt i
  -- TODO: do something with flags in char/string literals
  CConst (CCharConst (CChar c _) _) ->
    return $ Lit $ LitChar c
  -- TODO: this is temporary solution
  -- (makes the rest of the characters pointless)
  CConst (CCharConst (CChars (c:_) _) _) ->
    return $ Lit $ LitChar c
  CConst (CFloatConst (CFloat s) _) ->
    return $ Lit $ LitFloat s
  CConst (CStrConst (CString s _) _) ->
    return $ Lit $ LitStr s
  -- TODO: from here on
  -- CCompoundList
  -- CGenericSelection
  -- CStatExpr
  -- CLabAddrExpr
  -- CBuiltinExpr

instance Transform CExpr where
  -- the top-most binding should be first recursively (in comparison that would be the binding of ==, then operands and then their child bindings)
  transform expr = do
    anonName <- appendNextAnon (T.pack "@Expr")
    expr' <- transformExpr expr
    return [([],[[(anonName, [([],expr')])]])]  -- TODO

instance Transform CFunDef where
  transform funDef@(CFunDef _ (CDeclr (Just ident) _ _ _ _) _ _ _) = do
    let sId = getCName ident
    name <- sgName sId
    enterFunction sId
    funDef' <- transformFunDef funDef name
    leaveFunction
    return [funDef']

instance Transform CDecl where  -- TODO
  transform (CDecl specs declrs a) = do
    pureType <- translateDeclSpecs specs
    case declrs of  -- TODO
      (Just (CDeclr (Just ident) derivedDecls _ _ _), Nothing, Nothing):rest -> do
        let sId = getCName ident
        name <- sgName sId
        type' <- translateDerivedDecl pureType derivedDecls
        rest' <- transform (CDecl specs rest a)
        let scheme = toScheme type'
        return $ ([(name, scheme, [([], Const (name :>: scheme))])], []) : rest'
      (Just (CDeclr (Just ident) derivedDecls _ _ _), Just (CInitExpr cExpr _), Nothing):rest -> do
        let sId = getCName ident
        name <- sgName sId
        type' <- translateDerivedDecl pureType derivedDecls
        cExpr' <- transformExpr cExpr
        rest' <- transform (CDecl specs rest a)
        return $ ([(name, toScheme type', [([],cExpr')])], []) : rest'
      [] -> return []
  transform (CStaticAssert cExpr cStrLit _) = return []

instance Transform CStrLit where
  transform (CStrLit (CString s _) _) = do
    anonName <- appendNextAnon (T.pack "@CString")
    return [([],[[(anonName, [([],Lit $ LitStr s)])]])]  -- TODO

extractPar :: CDecl -> TState (Id, Type)
extractPar (CDecl declSpecs [(Nothing, _, _)] _) = do
  parName <- appendNextAnon (T.pack "@TODO")
  parType <- translateDeclSpecs declSpecs
  return (parName, parType)
extractPar (CDecl declSpecs [(Just (CDeclr Nothing derived _ _ _), _, _)] _) = do
  parName <- appendNextAnon (T.pack "@TODO")
  parType <- translateDeclSpecs declSpecs >>= flip translateDerivedDecl derived
  return (parName, parType)
extractPar (CDecl declSpecs [(Just (CDeclr (Just ident) derived _ _ _), _, _)] _) = do
  let parId = getCName ident
  parName <- sgName parId
  parType <- translateDeclSpecs declSpecs >>= flip translateDerivedDecl derived
  return (parName, parType)

transformFunDef :: CFunDef -> Id -> TState BindGroup
transformFunDef (CFunDef specs (CDeclr (Just (Ident sId _ _)) derivedDecls _ _ _) decls stmt _) name = do -- TODO
    let
      splitType fType = return $ case fType of
        (TAp (TAp arrowType parsTuple) rType) ->
          (parsTuple, rType)
        _ -> (tError, tError)
      typeSignatures = case head derivedDecls of
        -- old-style
        cFunDef@(CFunDeclr (Left idents) _ _) ->
          error $ niceError
            "Not supporting old-style functions"
            (nodeInfo cFunDef)  -- TODO
        -- not var-args
        CFunDeclr (Right (parDecls, False)) _ _ ->
          traverse extractPar parDecls
        -- var-args
        CFunDeclr (Right (parDecls, True)) _ _ ->
          traverse extractPar parDecls  -- TODO
        _ ->
          return []  -- TODO
      changeResult (TAp p r) to = TAp p to
    pureType <- translateDeclSpecs specs
    fType <- translateDerivedDecl pureType derivedDecls
    (parsType, retType) <- splitType fType
    paramsName <- sgName (T.pack "@Params")
    returnName <- sgName (T.pack "@Return")
    pars <- typeSignatures
    stmt' <- transform stmt
    returns <- getFunctionReturns
    reassemble . reverseExpls $
      ( [ ( name
          , if retType == tError then toScheme tError else toScheme fType
          , [ ( [ PCon
                    (paramsName :>: toScheme (tupleize (snd <$> pars)))
                    (PVar . fst <$> pars)
                ]
              , Let
                  (flattenProgram stmt')
                  $ foldl -- TODO: here we can do warning if retType is not tVoid and there is nothing to actually return
                    (\ a b -> Var returnFunc `Ap` a `Ap` b)
                    (Const $ returnName :>: toScheme retType)
                    returns
              )
            ]
          )
        ]
      , []
      )

beginCHMFunDef :: CHMHead -> Id -> TState Id
beginCHMFunDef chmHead name = do
    name' <- sgName name
    enterFunction name
    enterCHMHead
    transform_ chmHead
    return name'

instance Transform CHMFunDef where
  transform (CHMFunDef chmHead funDef _) = do
    name <- beginCHMFunDef chmHead (getCName funDef)
    rtrn <- transformFunDef funDef name >>= chmSchemize
    leaveCHMHead
    leaveFunction
    return [rtrn]

{- |
  Transforms a 'CHMFunDef' without making it generic,
  also creates variables for each type declared in the header
  (including aliases).
-}
class TransformCHMFunDef a where
  transformCHMFunDef :: a -> TState Program

instance TransformCHMFunDef CExtDecl where
  transformCHMFunDef (CHMFDefExt chmFunDef) =
    transformCHMFunDef chmFunDef

class GetAliases a where
  getAliases :: a -> TState [Assump]
  getAliasNames :: a -> [Id]

instance GetAliases CHMConstr where
  getAliases (CHMUnifyConstr ident chmType _) = do
    chmType' <- transformCHMType chmType
    return [getCName ident :>: toScheme chmType']
  getAliases _ = return []
  getAliasNames (CHMUnifyConstr ident chmType _) =
    [getCName ident]
  getAliasNames _ = []

instance GetAliases a => GetAliases [a] where
  getAliases as = concat <$> traverse getAliases as
  getAliasNames as = T.concat <$> traverse getAliasNames as

instance TransformCHMFunDef CHMFunDef where
  transformCHMFunDef (CHMFunDef chmHead@(CHMHead tVars chmConstrs _) funDef _) = do
    name <- beginCHMFunDef chmHead (getCName funDef)
    tVars' <- gets ((toScheme . TVar <$>) . reverse . head . typeVariables)
    let
      tVarNames = [ T.concat [name, T.singleton ':', getCName ident] | ident <- tVars]
    funDef' <- transformFunDef funDef name >>= replaceAliasize
    parExpls <- replaceAliasize $ zip3 tVarNames tVars' (repeat [])
    aliases <- ((\(i :>: sc) -> (T.concat [name, T.singleton ':', i], sc, [])) <$>) <$> getAliases chmConstrs
    leaveCHMHead
    leaveFunction
    return [funDef', (parExpls <> aliases, [])]

instance Transform CStat where
  transform cStat = case cStat of
    CLabel _ stmt _ _ -> transform stmt
    CCase cExpr stmt _ -> do
      switchName <- getSwitchName
      anonName <- appendNextAnon (T.pack "@Case")
      cExpr' <- transformExpr cExpr
      stmt' <- transform stmt
      return $ ([],[[(anonName, [([],ap2 (Var caseFunc) (Var switchName) cExpr')])]]) : stmt'
    CCases lExpr rExpr stmt _ -> do  -- TODO: add checking for range-ness
      switchName <- getSwitchName
      anonName <- appendNextAnon (T.pack "@Case")
      lExpr' <- transformExpr lExpr
      rExpr' <- transformExpr rExpr
      stmt' <- transform stmt
      return $ ([],[[(anonName, [([],ap2 (Var caseFunc) (Var switchName) lExpr'), ([],ap2 (Var caseFunc) (Var switchName) rExpr')])]]) : stmt'
    CDefault stmt _ -> transform stmt
    CExpr (Just expr) _ -> transform expr
    CExpr Nothing _ -> return []
    CCompound _ [] _ -> return []
    CCompound _ block _ -> do
      enterScope mempty
      block' <- transform block
      leaveScope
      return block'
    CIf expr tStmt (Just fStmt) _ -> do
      anonName <- appendNextAnon (T.pack "@IfElse")
      expr' <- transformExpr expr
      tStmt' <- transform tStmt
      fStmt' <- transform fStmt
      return $ ([], [[(anonName, [([], expr')])]]) : (tStmt' <> fStmt')  -- TODO
    CIf expr tStmt Nothing _ -> do
      anonName <- appendNextAnon (T.pack "@If")
      expr' <- transformExpr expr
      tStmt' <- transform tStmt
      return $ ([],[[(anonName, [([],expr')])]]) : tStmt'  -- TODO
    CSwitch expr stmt _ -> do
      enterSwitch
      name <- getSwitchName
      expr' <- transformExpr expr
      stmt' <- transform stmt
      leaveSwitch
      return $ ([],[[(name, [([],expr')])]]) : stmt'
    CWhile expr stmt _ _ -> do
      anonName <- appendNextAnon (T.pack "@While")
      expr' <- transformExpr expr
      stmt' <- transform stmt
      return $ ([],[[(anonName, [([],expr')])]]) : stmt'  -- TODO
    CFor (Left expr1) expr2 expr3 stmt a -> do
      anonNum <- T.pack . show <$> getNextAnon
      expr1' <- traverse transformExpr expr1
      let expr1'' = (\e -> (T.pack "@For:" <> anonNum, [([], e)])) <$>  expr1'
      expr2' <- traverse transformExpr expr2  -- TODO
      let expr2'' = (\e -> (T.pack "@ForCond:" <> anonNum, [([], e)])) <$> expr2'
      expr3' <- traverse transformExpr expr3
      let expr3'' = (\e -> (T.pack "@ForInc:" <> anonNum, [([], e)])) <$> expr3'
      stmt' <- transform stmt
      return $
        ( []
        , [catMaybes [expr1'', expr2'', expr3'']]
        ) : stmt'
    CFor (Right decl) expr2 expr3 stmt a -> do
      anonNum <- T.pack . show <$> getNextAnon
      enterScope mempty
      decl' <- transform decl
      let [([(name, scheme, alts)], _)] = decl'
      expr2' <- traverse transformExpr expr2  -- TODO
      let expr2'' = (\e -> (T.pack "@ForCond:" <> anonNum, [([], e)])) <$> expr2'
      expr3' <- traverse transformExpr expr3
      let expr3'' = (\e -> (T.pack "@ForInc:" <> anonNum, [([], e)])) <$> expr3'
      stmt' <- transform stmt
      leaveScope
      return $
        ( [(name, scheme, alts)]
        , [catMaybes [expr2'', expr3'']]
        ) : stmt'
    CGoto _ _ -> return []
    CGotoPtr _ _ -> return []  -- TODO
    CCont _ ->  return []
    CBreak _ -> return []
    CReturn (Just expr) _ -> do
      transformExpr expr >>= addFunctionReturn
      return []
    CReturn Nothing _ -> do
      addFunctionReturn (Lit LitVoid)
      return []
    CAsm _ _ -> return []

instance Transform CBlockItem where
  transform (CBlockStmt stmt) = transform stmt
  -- new variable
  transform (CBlockDecl cDecl) = transform cDecl
  transform (CNestedFunDef _) = return []  -- TODO: gnu thing, so maybe not-todo

fixKinds :: Type -> TState Type
fixKinds t = do
  let
    getAp (TAp t1 t2) =
      let
        (id, kind) = getAp t1
      in (id, Kfun Star kind)
    getAp (TVar (Tyvar id _)) = (id, Star)
    getAp _ = (mempty, Star)
    ap = getAp t
  state@TransformMonad
    { typeVariables = tVs
    } <- get
  let
    fix ts@(first@(Tyvar id1 kind1) : others) new@(id2, kind2)
      | id2 == mempty = ts
      | id1 == id2 = Tyvar id1 kind2 : others -- TODO
      | otherwise = first : fix others new
    fix [] _ = []
  put state
    { typeVariables = fix (head tVs) ap : tail tVs
    }
  let
    putAp t new@(id, kind)
      | id == mempty = t
      | otherwise = case t of
        (TAp t1 t2) -> TAp (putAp t1 new) t2
        (TVar (Tyvar _ _)) -> TVar $ Tyvar id kind
  return $ putAp t ap

-- | Transforms a 'CHMT' into its corresponding thih 'Type'
transformCHMType :: CHMT -> TState Type
transformCHMType (CHMCType declSpecs _) = translateDeclSpecs declSpecs
transformCHMType (CHMParType cType (CHMParams cTypes _) _) = do
  cType' <- transformCHMType cType
  cTypes' <- traverse transformCHMType cTypes
  let
    apT = foldl TAp cType' cTypes'
  fixKinds apT

transformConstraint :: CHMConstr -> TState (Maybe Pred)
transformConstraint constr =
  case constr of
    (CHMClassConstr ident cTypes _) -> do
      let count = length cTypes
      cTypes' <- traverse transformCHMType cTypes
      return . Just . IsIn (getCName ident) $ createParamsType cTypes'
    (CHMUnifyConstr ident cType _) -> do
      cType' <- transformCHMType cType
      sgName (getCName ident) >>= flip chmAddAlias cType'
      return Nothing

translateConstraints :: [CHMConstr] -> TState ()
translateConstraints = mapM_ (transformConstraint >=> mapM_ chmAddClass)

instance Transform CHMHead where
  transform (CHMHead [] [] _) = return []
  transform (CHMHead types [] _) = sequence_
    [ do
      scopedId <- sgName $ getCName ident
      chmAddVariable $ Tyvar scopedId Star
    | ident <- types
    ] >> return []
  transform (CHMHead types constraints a) = do
    transform (CHMHead types [] a)
    translateConstraints constraints
    return []

transformStructHead :: Id -> CHMHead -> TState ()
transformStructHead name chmHead@(CHMHead types constraints nInfo) = do
    transform (CHMHead types [] nInfo)
    registered <- registerStruct name nInfo
    unless registered . error $ niceError
      "Struct redefinition"
      (nodeInfo chmHead)
    translateConstraints constraints

instance Transform CHMStructDef where
  transform (CHMStructDef chmHead (CStruct _ (Just ident) (Just cDecls) _ _) nInfo) = do
    let sId = getCName ident
    enterCHMHead
    transformStructHead sId chmHead
    registerCHMStructMembers sId cDecls
    leaveCHMHead
    return []

{- |
  Registers a new class and declares its content,
  adds an entry for each declaration to the transform monad
  (as we have to remember them when making instances of the class)
-}
declareClassContents :: Id -> [CExtDecl] -> TState [Expl]
declareClassContents id cExtDecls = do
  registered <- registerClass id
  let
    onlyPureMsg = "Currently only pure declarations allowed here"
    classDeclare (CDeclExt cDecl) = do
      let
        onlyPureDeclarationError = niceError onlyPureMsg $ nodeInfo cDecl
        translateDeclaration ([(name, Forall [] ([] :=> t), [([], Const (name2 :>: _))])], []) = do
          unless (name == name2) $ error onlyPureDeclarationError
          scheme <- chmScheme t
          registerClassDeclaration id (name :>: scheme)
          return (name, scheme, [])
        translateDeclaration as = error onlyPureDeclarationError
      transform cDecl >>= traverse translateDeclaration
    classDeclare c = error . niceError onlyPureMsg $ nodeInfo c
  if registered then concat <$> traverse classDeclare cExtDecls
  else error $ "Class " <> T.unpack id <> " redefined"

instance Transform CHMCDef where
  transform (CHMCDef ident chmHead cExtDecls _) = do
    enterCHMHead
    chmHead' <- transform chmHead
    expls <- declareClassContents (getCName ident) cExtDecls
    leaveCHMHead
    return [(expls, [])]

{- |
  Translates definitions inside Instance blocks
-}
defineInstanceContents :: Id -> CHMParams -> [CExtDecl] -> TState BindGroup
defineInstanceContents id (CHMParams chmTypes _) cExtDecls = do
  parType <- traverse transformCHMType chmTypes >>= replaceAliases . createParamsType
  let
    instanceDefine (CFDefExt f) =
      instanceDefine . CHMFDefExt $ CHMFunDef
        (CHMHead [] [] $ nodeInfo f)
        f
        (nodeInfo f)
    instanceDefine (CHMFDefExt f) = do
      f' <- transform f
      let [([(name, scheme, def)],[])] = f'
      mScheme <- getMethodScheme id name
      name' <- registerMethodInstance id name parType
      case mScheme of
        Just scheme' -> return ([(name', scheme, ([], Var name) : def)], [])
        Nothing -> error $ niceError
          "Cannot define given instance method"
          (nodeInfo f)
    instanceDefine cExtDecl = error $ niceError
      "Instances can currently contain only method definitions"
      (nodeInfo cExtDecl)
  flattenProgram <$> traverse instanceDefine cExtDecls

instance Transform CHMIDef where
  transform (CHMIDef id chmPars cExtDecls nInfo) =
    transform (CHMIDefHead id (CHMHead [] [] nInfo) chmPars cExtDecls nInfo)
  transform (CHMIDefHead ident chmHead chmPars cExtDecls _) = do
    enterCHMHead
    chmHead' <- transform chmHead
    rtrn <- defineInstanceContents (getCName ident) chmPars cExtDecls
    leaveCHMHead
    return [rtrn]

class ReplaceAliasize a where
  replaceAliasize :: a -> TState a

instance ReplaceAliasize Type where
  replaceAliasize = replaceAliases

instance ReplaceAliasize Assump where
  replaceAliasize (id :>: scheme) =
    (id :>:) <$> replaceAliasize scheme

instance ReplaceAliasize Scheme where
  replaceAliasize (Forall kinds (cs :=> t)) = do
    cs' <- replaceAliasize cs
    t' <- replaceAliasize t
    return (Forall kinds (cs' :=> t'))

instance ReplaceAliasize Pred where
  replaceAliasize (IsIn id t) =
    IsIn id <$> replaceAliasize t

instance ReplaceAliasize BindGroup where
  replaceAliasize (expls, impls) = do
    expls' <- replaceAliasize expls
    impls' <- replaceAliasize impls
    return (expls', impls')

instance ReplaceAliasize Expl where
  replaceAliasize (id, scheme, alts) = do
    scheme' <- replaceAliasize scheme
    alts' <- replaceAliasize alts
    return (id, scheme', alts')

instance ReplaceAliasize Impl where
  replaceAliasize (id, alts) = do
    alts' <- replaceAliasize alts
    return (id, alts')

instance ReplaceAliasize Alt where
  replaceAliasize (pats, expr) = do
    pats' <- replaceAliasize pats
    expr' <- replaceAliasize expr
    return (pats', expr')

instance ReplaceAliasize Pat where
  replaceAliasize (PCon assump pats) = do
    assump' <- replaceAliasize assump
    pats' <- replaceAliasize pats
    return (PCon assump' pats')
  -- PVar, PWildcard, PLit, PNpk
  replaceAliasize pat = return pat

instance ReplaceAliasize Expr where
  replaceAliasize (Const assump) =
    Const <$> replaceAliasize assump
  replaceAliasize (Ap expr1 expr2) = do
    expr1' <- replaceAliasize expr1
    expr2' <- replaceAliasize expr2
    return (Ap expr1' expr2')
  replaceAliasize (Let bindGroup expr) = do
    bindGroup' <- replaceAliasize bindGroup
    expr' <- replaceAliasize expr
    return (Let bindGroup' expr')
  replaceAliasize (Lambda alt) =
    Lambda <$> replaceAliasize alt
  replaceAliasize (LambdaScheme scheme alt) = do
    scheme' <- replaceAliasize scheme
    alt' <- replaceAliasize alt
    return (LambdaScheme scheme' alt')
  -- Var, Lit
  replaceAliasize expr = return expr

instance ReplaceAliasize a => ReplaceAliasize [a] where
  replaceAliasize = traverse replaceAliasize

mangleAnonType :: CDeclSpec -> TState Id
mangleAnonType (CHMAnonType nInfo) = do
  posMap <- gets posData
  case nInfo `Map.lookup` posMap of
    Just (PosAnonData i) -> return (T.pack ("@Anon" <> show i))
    Nothing -> do
      anonNum <- getNextAnon
      modify (\state -> state{posData=Map.insert nInfo (PosAnonData anonNum) posMap})
      return . T.pack $ "@Anon" <> show anonNum
