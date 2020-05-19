{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module CHM.Transform
  ( Transform (..)
  , TransformCHMFunDef (..)
  , TState
  , TransformMonad (..)
  , runInfer
  , initTransformMonad
  , getTransformResult
  , typeInfer
  ) where

import Control.Monad.State
import Control.Monad((>=>), when)
import qualified Data.Set as Set

import TypingHaskellInHaskell

import Language.C.Data
import Language.C.Syntax
import Language.C.Data.Ident (Ident(..))

import CHM.TransformMonad

class Transform a where
  transform :: a -> TState Program

getTransformResult :: Transform a => a -> Program
getTransformResult = fst . runTState . transform

typeInfer :: [Assump] -> Program -> TState [Assump]
typeInfer assumps program = do
  TransformMonad{builtIns = bIs, memberClasses = mCs}  <- get
  case mCs initialEnv of
    Nothing -> return $ error "Environment corrupted"
    Just cEnv -> return $ tiProgram cEnv (Set.toList bIs ++ assumps) program

runInfer :: Transform a => a -> [Assump]
runInfer a =
  let
    (program, TransformMonad{memberClasses=mCs, builtIns=bIs}) =
      runTState . transform $ a
  in
    case mCs initialEnv of
      Nothing -> ["@programEnvironment" :>: toScheme tError]  -- TODO: but I like it like it is
      Just env -> tiProgram env (Set.toList bIs) program

-- | Takes a `Program` and flattens it into a `BindGroup`
flattenProgram :: Program -> BindGroup
flattenProgram ((expls, impls) : rest) =
  let
    (restExpls, restImpls) = flattenProgram rest
  in (expls ++ restExpls, impls ++ restImpls)
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
      innerName = "@INNER_" ++ eName
    bindGroup' <- reassemble ([(innerName, eScheme', [(PVar eName : pats, Let (rest, impls) returnValue)])], [])
    others <- transformPars pats
    return . flattenProgram $ [([(name, scheme, [(pats, foldl Ap (Var innerName) (expr : others))])], []), bindGroup']
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
      impls' <- chmSchemize impls
      return (expls', impls')

instance CHMSchemize a => CHMSchemize [a] where
  chmSchemize = traverse chmSchemize

instance CHMSchemize Expl where
  chmSchemize (name, scheme, alts) = do
    scheme' <- chmSchemize scheme
    alts' <- chmSchemize alts
    return (name, scheme', alts')

instance CHMSchemize Impl where
  chmSchemize (name, alts) = (,) name <$> chmSchemize alts

instance CHMSchemize Alt where
  chmSchemize (pats, expr) = (,) pats <$> chmSchemize expr

instance CHMSchemize Expr where
  chmSchemize (Let bindGroup expr) = do
    bindGroup' <- chmSchemize bindGroup
    expr' <- chmSchemize expr
    return $ Let bindGroup' expr'
  chmSchemize (Const assump) = Const <$> chmSchemize assump
  chmSchemize (Ap expr1 expr2) = do
    expr1' <- chmSchemize expr1
    expr2' <- chmSchemize expr2
    return $ Ap expr1' expr2'
  -- case for Var and Lit
  chmSchemize expr = return expr

instance CHMSchemize Assump where
  chmSchemize (id :>: scheme) = (id :>:) <$> chmSchemize scheme

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
  CTypeSpec (CLongType _) -> return tLong  -- TODO "long long int" will just return "long"
  CTypeSpec (CFloatType _) -> return tFloat
  CTypeSpec (CDoubleType _) -> return tDouble
  CTypeSpec (CSignedType _) -> return tSigned
  CTypeSpec (CUnsigType _) -> return tUnsig
  CTypeSpec (CBoolType _) -> return tBool
  CTypeSpec (CComplexType _) -> return tComplex
  CTypeSpec (CInt128Type _) -> return tInt128
  CTypeSpec (CSUType (CStruct CStructTag (Just (Ident sId _ _)) Nothing _ _) _) -> return $ TCon (Tycon sId (Kfun Star Star))  -- TODO: same as TypeDef (just few rows below)
  CTypeSpec (CSUType (CStruct CStructTag (Just (Ident sId _ _)) (Just cDecls) _ _) _) -> registerStructMembers sId cDecls >> return (TCon (Tycon sId Star))
  CTypeSpec (CSUType (CStruct CStructTag Nothing _ _ _) _ ) -> return tError  -- TODO
  CTypeSpec (CSUType (CStruct CUnionTag (Just (Ident sId _ _)) _ _ _) _) -> return $ TCon (Tycon sId Star)  -- TODO: same as TypeDef
  CTypeSpec (CSUType (CStruct CUnionTag Nothing _ _ _) _) -> return tError  -- TODO
  CTypeSpec (CTypeDef (Ident sId _ _) _) -> do
    name <- scopedName sId
    return $ TVar (Tyvar name Star)  -- TODO: why just Star, we should store it in the monad (and the name as well)
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

extractParameters :: [CDecl] -> TState Program
extractParameters (decl:decls) = case decl of
    CDecl declSpecs [] _ ->
      extractParameters decls
    CDecl declSpecs [(Nothing, _, _)] _ ->
      extractParameters decls
    CDecl declSpecs [(Just (CDeclr Nothing derived _ _ _), _, _)] _ ->
      extractParameters decls
    CDecl declSpecs [(Just (CDeclr (Just (Ident sId _ _)) derived _ _ _), _, _)] _ -> do
      name <- sgName sId
      others <- extractParameters decls
      pureType <- translateDeclSpecs declSpecs
      expandedType <- translateDerivedDecl pureType derived
      return $ ([(name, toScheme expandedType, [])], []) : others
extractParameters [] = return []

registerStructMembers :: Id -> [CDecl] -> TState ()
registerStructMembers _ [] = return ()
registerStructMembers id cDecls = do
  registered <- registerStruct id
  let
    registerSingleCDecl (CDecl specs declrs a) =
      case declrs of
        (Just (CDeclr (Just (Ident mId _ _)) derivedDecls _ _ _), Nothing, Nothing):rest -> do
          pureType <- translateDeclSpecs specs
          type' <- translateDerivedDecl pureType derivedDecls
          registerMember id mId type'
          registerSingleCDecl (CDecl specs rest a)
        (Just (CDeclr (Just (Ident mId _ _)) derivedDecls _ _ _), Just _, Nothing):rest ->
          registerSingleCDecl (CDecl specs rest a)  -- TODO: this is probably error (but still recognized by c++ as kosher)
        [] -> return ()
  when registered $ sequence_ (registerSingleCDecl <$> cDecls)

registerCHMStructMembers :: Id -> [CDecl] -> TState ()
registerCHMStructMembers _ [] = return ()
registerCHMStructMembers id cDecls = do
  registered <- registerStruct id
  let
    registerSingleCDecl (CDecl specs declrs a) =
      case declrs of
        (Just (CDeclr (Just (Ident mId _ _)) derivedDecls _ _ _), Nothing, Nothing):rest -> do
          pureType <- translateDeclSpecs specs
          type' <- translateDerivedDecl pureType derivedDecls
          registerCHMMember id mId type'
          registerSingleCDecl (CDecl specs rest a)
        (Just (CDeclr (Just (Ident mId _ _)) derivedDecls _ _ _), Just _, Nothing):rest ->
          registerSingleCDecl (CDecl specs rest a)  -- TODO: this is probably error (but still recognized by c++ as kosher)
        _ -> return ()
  when registered $ sequence_ (registerSingleCDecl <$> cDecls)

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
  -- TODO: CCast
  CUnary op expr _ -> do
    expr' <- transformExpr expr
    return $ Ap
      (Var $ operatorFunction op)
      expr'
  -- TODO: CSizeofExpr
  -- TODO: CSizeofType
  -- ditto align
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
  CVar (Ident sId _ _) _ -> do
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
    anonName <- appendNextAnon "@Expr"
    expr' <- transformExpr expr
    return [([],[[(anonName, [([],expr')])]])]  -- TODO

instance Transform CFunDef where
  transform funDef@(CFunDef _ (CDeclr (Just (Ident sId _ _)) _ _ _ _) _ _ _) = do
    name <- sgName sId
    enterFunction sId
    funDef' <- transformFunDef funDef name
    leaveFunction
    return [funDef']

instance Transform CDecl where  -- TODO
  transform (CDecl specs declrs a) = do
    pureType <- translateDeclSpecs specs
    case declrs of  -- TODO
      (Just (CDeclr (Just (Ident sId _ _)) derivedDecls _ _ _), Nothing, Nothing):rest -> do
        name <- sgName sId
        type' <- translateDerivedDecl pureType derivedDecls
        rest' <- transform (CDecl specs rest a)
        return $ ([(name, toScheme type', [])], []) : rest'
      (Just (CDeclr (Just (Ident sId _ _)) derivedDecls _ _ _), Just (CInitExpr cExpr _), Nothing):rest -> do
        name <- sgName sId
        type' <- translateDerivedDecl pureType derivedDecls
        cExpr' <- transformExpr cExpr
        rest' <- transform (CDecl specs rest a)
        return $ ([(name, toScheme type', [([],cExpr')])], []) : rest'
      [] -> return []
  transform (CStaticAssert cExpr cStrLit _) = return []

instance Transform CStrLit where
  transform (CStrLit (CString s _) _) = do
    anonName <- appendNextAnon "@CString"
    return [([],[[(anonName, [([],Lit $ LitStr s)])]])]  -- TODO

extractParNames :: [CDecl] -> TState [Id]
extractParNames (parDecl:parDecls) =
  case parDecl of
    CDecl declSpecs [(Nothing, _, _)] _ -> do
      anonName <- appendNextAnon "@TODO"
      (anonName:) <$> extractParNames parDecls
    CDecl declSpecs [(Just (CDeclr Nothing derived _ _ _), _, _)] _ -> do
      anonName <- appendNextAnon "@TODO"
      (anonName:) <$> extractParNames parDecls
    CDecl declSpecs [(Just (CDeclr (Just (Ident parId _ _)) derived _ _ _), _, _)] _ -> do
      pName <- sgName parId
      (pName:) <$> extractParNames parDecls
extractParNames [] = return []

transformFunDef :: CFunDef -> Id -> TState BindGroup
transformFunDef (CFunDef specs (CDeclr (Just (Ident sId _ _)) derivedDecls _ _ _) decls stmt _) name = do -- TODO
    let
      splitType fType = return $ case fType of
        (TAp (TAp arrowType parsTuple) rType) ->
          (parsTuple, rType)
        _ -> (tError, tError)
      typeSignatures = case head derivedDecls of
        -- old-style
        CFunDeclr (Left idents) _ _ ->
          return [parId | Ident parId _ _ <- idents]  -- TODO
        -- not var-args
        CFunDeclr (Right (parDecls, False)) _ _ ->
          extractParNames parDecls
        -- var-args
        CFunDeclr (Right (parDecls, True)) _ _ ->
          extractParNames parDecls  -- TODO
        _ ->
          return []  -- TODO
      changeResult (TAp p r) to = TAp p to
    pureType <- translateDeclSpecs specs
    fType <- translateDerivedDecl pureType derivedDecls
    (parsType, retType) <- splitType fType
    paramsName <- sgName "@Params"
    returnName <- sgName "@Return"
    parIds <- typeSignatures
    stmt' <- transform stmt
    returns <- getFunctionReturns
    reassemble . reverseExpls $
      ( [ ( name
          , if retType == tError then toScheme tError else toScheme fType
          , [ ( [ PCon
                    (paramsName :>: getTupleCon (length parIds))
                    (PVar <$> parIds)
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

instance Transform CHMFunDef where
  transform (CHMFunDef chmHead funDef@(CFunDef _ (CDeclr (Just (Ident sId _ _)) _ _ _ _) _ _ _) _) = do
    name <- sgName sId
    enterFunction sId
    enterCHMHead
    chmHead' <- transform chmHead
    rtrn <- transformFunDef funDef name >>= chmSchemize
    leaveCHMHead
    leaveFunction
    return [rtrn]

class TransformCHMFunDef a where
  transformCHMFunDef :: a -> TState Program

instance TransformCHMFunDef CExtDecl where
  transformCHMFunDef (CHMFDefExt chmFunDef) =
    transformCHMFunDef chmFunDef

instance TransformCHMFunDef CHMFunDef where
  transformCHMFunDef (CHMFunDef chmHead funDef@(CFunDef _ (CDeclr (Just (Ident sId _ _)) _ _ _ _) _ _ _) _) = do
    name <- sgName sId
    enterFunction sId
    enterCHMHead
    chmHead' <- transform chmHead
    rtrn <- transformFunDef funDef name
    leaveCHMHead
    leaveFunction
    return [rtrn]

instance Transform CStat where
  transform cStat = case cStat of
    CLabel _ stmt _ _ -> transform stmt
    CCase cExpr stmt _ -> do
      switchName <- getSwitchName
      anonName <- appendNextAnon "@Case"
      cExpr' <- transformExpr cExpr
      stmt' <- transform stmt
      return $ ([],[[(anonName, [([],ap2 (Var caseFunc) (Var switchName) cExpr')])]]) : stmt'
    CCases lExpr rExpr stmt _ -> do  -- TODO: add checking for range-ness
      switchName <- getSwitchName
      anonName <- appendNextAnon "@Case"
      lExpr' <- transformExpr lExpr
      rExpr' <- transformExpr rExpr
      stmt' <- transform stmt
      return $ ([],[[(anonName, [([],ap2 (Var caseFunc) (Var switchName) lExpr'), ([],ap2 (Var caseFunc) (Var switchName) rExpr')])]]) : stmt'
    CDefault stmt _ -> transform stmt
    CExpr (Just expr) _ -> transform expr
    CExpr Nothing _ -> return []
    CCompound _ [] _ -> return []
    CCompound _ block _ -> do
      enterScope []
      block' <- transform block
      leaveScope
      return block'
    CIf expr tStmt (Just fStmt) _ -> do
      anonName <- appendNextAnon "@IfElse"
      expr' <- transformExpr expr
      tStmt' <- transform tStmt
      fStmt' <- transform fStmt
      return $ ([],[[(anonName, [([],expr')])]]) : (tStmt' ++ fStmt')  -- TODO
    CIf expr tStmt Nothing _ -> do
      anonName <- appendNextAnon "@If"
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
      anonName <- appendNextAnon "@While"
      expr' <- transformExpr expr
      stmt' <- transform stmt
      return $ ([],[[(anonName, [([],expr')])]]) : stmt'  -- TODO
    CFor _ _ _ a _ -> return []  -- TODO
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
    getAp _ = ([], Star)
    ap = getAp t
  state@TransformMonad
    { typeVariables = tVs
    } <- get
  let
    fix ts ([],_) = ts
    fix (first@(Tyvar id1 kind1) : others) new@(id2, kind2)
      | id1 == id2 = Tyvar id1 kind2 : others -- TODO
      | otherwise = first : fix others new
    fix [] _ = []
  put state
    { typeVariables = fix (head tVs) ap : tail tVs
    }
  let
    putAp t1 ([], _) = t1
    putAp (TAp t1 t2) new = TAp (putAp t1 new) t2
    putAp (TVar (Tyvar _ _)) (id, kind) = TVar $ Tyvar id kind
  return $ putAp t ap

translateCHMType :: CHMT -> TState Type
translateCHMType (CHMCType declSpecs _) = translateDeclSpecs declSpecs
translateCHMType (CHMParType cType (CHMParams cTypes _) _) = do
  cType' <- translateCHMType cType
  cTypes' <- traverse translateCHMType cTypes
  let
    apT = foldl TAp cType' cTypes'
  fixKinds apT

transformConstraint :: CHMConstr -> TState (Maybe Pred)
transformConstraint constr =
  case constr of
    (CHMClassConstr (Ident id _ _) cTypes _) -> do
      let count = length cTypes
      cTypes' <- traverse translateCHMType cTypes
      return . Just . IsIn id $ createParamsType cTypes'
    (CHMUnifyConstr (Ident id _ _) cType _) -> do
      cType' <- translateCHMType cType
      sgName id >>= flip chmAddAlias cType'
      return Nothing

translateConstraints :: [CHMConstr] -> TState ()
translateConstraints = mapM_ (transformConstraint >=> mapM_ chmAddClass)

instance Transform CHMHead where
  transform (CHMHead [] [] _) = return []
  transform (CHMHead types [] _) = sequence_
    [ do
      scopedId <- sgName id
      chmAddVariable $ Tyvar scopedId Star
    | Ident id _ _ <- types
    ] >> return []
  transform (CHMHead types constraints a) = do
    transform (CHMHead types [] a)
    translateConstraints constraints
    return []

instance Transform CHMStructDef where
  -- TODO
  transform (CHMStructDef chmHead (CStruct CStructTag (Just (Ident sId _ _)) (Just cDecls) _ _) _) = do
    enterCHMHead
    chmHead' <- transform chmHead
    registerCHMStructMembers sId cDecls
    leaveCHMHead
    return []

{- |
  Registers a new class and declares its content,
  adds an entry for each declaration to the transform monad
  (as we have to remember them when making instances of the class)
  TODO: this looks too obfuscated (more so than how haskell usually looks)
-}
declareClassContents :: Id -> [CExtDecl] -> TState [Expl]
declareClassContents id cExtDecls = do
  registered <- registerClass id
  let
    classDeclare (CDeclExt cDecl) = do
      let
        translateDeclaration ([(name, Forall [] ([] :=> t), [])], []) = do
          scheme <- chmScheme t
          registerClassDeclaration id (name :>: scheme)
          return (name, scheme, [])
        translateDeclaration _ = return $ error "only pure declarations allowed here"
      transform cDecl >>= traverse translateDeclaration
    classDeclare _ = return $ error "only declarations allowed in class declarations"
  if registered then concat <$> traverse classDeclare cExtDecls
  else return $ error "class already defined"

instance Transform CHMCDef where
  transform (CHMCDef (Ident cId _ _) chmHead cExtDecls _) = do
    enterCHMHead
    chmHead' <- transform chmHead
    expls <- declareClassContents cId cExtDecls
    leaveCHMHead
    return [(expls, [])]

{- |
  Translates definitions inside Instance blocks
-}
defineInstanceContents :: Id -> CHMParams -> [CExtDecl] -> TState BindGroup
defineInstanceContents id (CHMParams chmTypes _) cExtDecls = do
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
      parType <- createParamsType <$> traverse translateCHMType chmTypes
      name' <- registerMethodInstance id name parType
      case mScheme of
       Just scheme' -> return ([(name', scheme, ([], Var name) : def)], [])
       Nothing -> return $ error "Cannot define given instance method"
    instanceDefine _ = return $ error "Instances shall contain only method definitions"
  flattenProgram <$> traverse instanceDefine cExtDecls

instance Transform CHMIDef where
  transform (CHMIDef id chmPars cExtDecls nInfo) =
    transform (CHMIDefHead id (CHMHead [] [] nInfo) chmPars cExtDecls nInfo)
  transform (CHMIDefHead (Ident iId _ _) chmHead chmPars cExtDecls _) = do
    enterCHMHead
    chmHead' <- transform chmHead
    rtrn <- defineInstanceContents iId chmPars cExtDecls
    leaveCHMHead
    return [rtrn]
