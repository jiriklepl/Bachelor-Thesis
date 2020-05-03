{-# LANGUAGE FlexibleInstances, FlexibleContexts #-}
module CHM.Transform where

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

typeInfer :: Transform a => a -> [Assump]
typeInfer a =
  let
    (program, TransformMonad{memberClasses=mcs, builtIns=bis}) =
      runTState . transform $ a
  in
    case mcs initialEnv of
      Nothing -> ["@programEnvironment" :>: toScheme tError]  -- TODO: but I like it like it is
      Just env -> tiProgram env (Set.toList bis) program

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
reassemble bindGroup@([(name,scheme,[(pats, Let (expls, impls) returnValue)])], []) = case expls of
  (eName, eScheme, [([],expr)]) : rest ->
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
    in do
      bindGroup' <- reassemble ([("TODO_" ++ eName, eScheme', [(PVar eName : pats, Let (rest, impls) returnValue)])], [])
      others <- transformPars pats
      return ([(name,scheme,[(pats, Let bindGroup' $ foldl Ap (Var ("TODO_" ++ eName)) (expr : others))])], [])
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
translateDerivedDecl t (dDecl:dDecls) =
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
  in do
    t' <- translateDerivedDecl t dDecls
    case dDecl of
      CPtrDeclr typeQuals _ -> return $ translateQuals (pointer t') typeQuals
      CArrDeclr typeQuals _ _ -> return $ translateQuals (pointer t') typeQuals  -- TODO: this is just temporary
      -- old-style functions
      CFunDeclr (Left _) _ _ -> return tError  -- TODO
      -- new-style functions (non-variadic)
      CFunDeclr (Right (rawDecls, False)) _ _ ->
        let
          decls = (extractDecls <$> rawDecls)
          translatesDerivedDecl (decl:otherDecls) = do
            pureType <- translateDeclSpecs $ fst decl
            transFirst <- translateDerivedDecl pureType (snd decl)
            transRest <- translatesDerivedDecl otherDecls
            return $ transFirst : transRest
          translatesDerivedDecl [] = return []
        in do
          types <- translatesDerivedDecl decls
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
      storeName sId
      name <- scopedName sId
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
          transType <- translateDerivedDecl pureType derivedDecls
          registerMember id mId transType
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
          transType <- translateDerivedDecl pureType derivedDecls
          registerCHMMember id mId transType
          registerSingleCDecl (CDecl specs rest a)
        (Just (CDeclr (Just (Ident mId _ _)) derivedDecls _ _ _), Just _, Nothing):rest ->
          registerSingleCDecl (CDecl specs rest a)  -- TODO: this is probably error (but still recognized by c++ as kosher)
        _ -> return ()
  when registered $ sequence_ (registerSingleCDecl <$> cDecls)


instance Transform CTranslUnit where
  transform (CTranslUnit [] _) = return []
  transform (CTranslUnit extDecls a) = concat <$> traverse transform extDecls

instance Transform CExtDecl where
  transform  (CDeclExt a)   = transform a
  transform  (CFDefExt a)   = transform a
  transform  (CHMFDefExt a) = transform a
  transform  (CHMSDefExt a) = transform a
  transform  (CHMCDefExt a) = transform a
  transform  (CHMIDefExt a) = transform a
  transform  (CAsmExt  a _) = transform a

-- these are better than the corresponding foldl because of the stronger type safety
ap2 :: Expr -> Expr -> Expr -> Expr
ap3 :: Expr -> Expr -> Expr -> Expr -> Expr

ap2 f a b = foldl Ap f [a, b]
ap3 f a b c = foldl Ap f [a, b, c]

transformExpr :: CExpr -> TState Expr
transformExpr cExpr = let
  in case cExpr of
  -- exprs is guaranteed to have at least 2 elements
  CComma exprs _ -> do
    transs <- traverse transformExpr exprs
    return $ foldl1
      (\a b -> Ap (Ap (Var commaOpFunc) a) b)
      transs
  CAssign op lExpr rExpr _ -> do
    lTrans <- transformExpr lExpr
    rTrans <- transformExpr rExpr
    return $ ap2
      (Var $ operatorFunction op)
      lTrans
      rTrans
  -- this is the ternary operator
  CCond cExpr (Just tExpr) fExpr _ -> do
    cTrans <- transformExpr tExpr
    tTrans <- transformExpr tExpr
    fTrans <- transformExpr fExpr
    return $ ap3
      (Var ternaryOpFunc)
      cTrans
      tTrans
      fTrans
  -- this is elvis (supported by gnu)
  CCond cExpr Nothing fExpr _ -> do
    cTrans <- transformExpr cExpr
    fTrans <- transformExpr fExpr
    return $ ap2
      (Var elvisOpFunc)
      cTrans
      fTrans
  CBinary op lExpr rExpr _ -> do
    lTrans <- transformExpr lExpr
    rTrans <- transformExpr rExpr
    return $ Var (operatorFunction op) `Ap` lTrans `Ap` rTrans
  -- TODO: CCast
  CUnary op expr _ -> do
    trans <- transformExpr expr
    return $ Ap
      (Var $ operatorFunction op)
      trans
  -- TODO: CSizeofExpr
  -- TODO: CSizeofType
  -- ditto align
  -- TODO: CComplexReal
  CIndex aExpr iExpr _ -> do
    aTrans <- transformExpr aExpr
    iTrans <- transformExpr iExpr
    return $ ap2
      (Var indexOpFunc)
      aTrans
      iTrans
  CCall func exprs _ -> do
    tuple <- getTuple (length exprs)
    fTrans <- transformExpr func
    eTrans <- traverse transformExpr exprs
    return $ Ap
      fTrans
      (foldl Ap (Var tuple) eTrans)
  -- sExpr->mId
  CMember sExpr mId True _ -> do
    member <- getMember mId
    sTrans <- transformExpr sExpr
    return $ Ap
      (Var member)
      (deref sTrans)
  -- sExpr.mId
  CMember sExpr mId False _ -> do
    member <- getMember mId
    sTrans <- transformExpr sExpr
    return $ Ap
      (Var member)
      sTrans
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
  transform cExpr = do
    anonNumber <- getNextAnon
    expr <- transformExpr cExpr
    return [([],[[("@Expr" ++ show anonNumber, [([],expr)])]])]  -- TODO

instance Transform CFunDef where  -- TODO: make this and CHMFunDef use same bits of code, also: make this work
  transform funDef@(CFunDef specs _ _ _ a) =
    transform (CHMFunDef (CHMHead [] [] a) funDef a)

instance Transform CDecl where  -- TODO
  transform (CDecl specs declrs a) = do
    pureType <- translateDeclSpecs specs
    case declrs of  -- TODO
      (Just (CDeclr (Just (Ident sId _ _)) derivedDecls _ _ _), Nothing, Nothing):rest -> do
        storeName sId
        name <- scopedName sId
        transType <- translateDerivedDecl pureType derivedDecls
        restTrans <- transform (CDecl specs rest a)
        return $ ([(name, toScheme transType, [])], []) : restTrans
      (Just (CDeclr (Just (Ident sId _ _)) derivedDecls _ _ _), Just (CInitExpr cExpr _), Nothing):rest -> do
        storeName sId
        name <- scopedName sId
        transType <- translateDerivedDecl pureType derivedDecls
        transExpr <- transformExpr cExpr
        restTrans <- transform (CDecl specs rest a)
        return $ ([(name, toScheme transType, [([],transExpr)])], []) : restTrans
      [] -> return []
  transform (CStaticAssert cExpr cStrLit _) = return []

instance Transform CStrLit where
  transform (CStrLit (CString s _) _) = do
    anonNumber <- getNextAnon
    return [([],[[("@CString" ++ show anonNumber, [([],Lit $ LitStr s)])]])]  -- TODO

instance Transform CHMFunDef where
  transform (CHMFunDef chmHead (CFunDef specs (CDeclr (Just (Ident sId _ _)) derivedDecls _ _ _) decls stmt _) _) =  -- TODO
    let
      extractPars (parDecl:parDecls) =
        case parDecl of
          CDecl declSpecs [(Nothing, _, _)] _ -> do
            anonNumber <- getNextAnon
            (("@TODO" ++ show anonNumber):) <$> extractPars parDecls
          CDecl declSpecs [(Just (CDeclr Nothing derived _ _ _), _, _)] _ -> do
            anonNumber <- getNextAnon
            (("@TODO" ++ show anonNumber):) <$> extractPars parDecls
          CDecl declSpecs [(Just (CDeclr (Just (Ident parId _ _)) derived _ _ _), _, _)] _ -> do
            storeName parId
            name <- scopedName parId
            (name:) <$> extractPars parDecls
      extractPars [] = return []
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
          extractPars parDecls
        -- var-args
        CFunDeclr (Right (parDecls, True)) _ _ ->
          extractPars parDecls  -- TODO
        _ ->
          return []  -- TODO
      changeResult (TAp p r) to = TAp p to
    in do
      storeName sId
      name <- scopedName sId
      enterFunction sId
      enterCHMHead
      transHead <- transform chmHead
      pureType <- translateDeclSpecs specs
      fType <- translateDerivedDecl pureType derivedDecls
      (parsType, retType) <- splitType fType
      storeName "@Params"
      paramsName <- scopedName "@Params"
      storeName "@Return"
      returnName <- scopedName "@Return"
      parIds <- typeSignatures
      transStmt <- transform stmt
      returns <- getFunctionReturns
      rtrn <- pure <$> (reassemble ( reverseExpls
        ( [ ( name
            , if retType == tError then toScheme tError else toScheme fType
            , [ ( [ PCon
                      (paramsName :>: getTupleCon (length parIds))
                      (PVar <$> parIds)
                  ]
                , Let
                    (flattenProgram transStmt)
                    $ foldl -- TODO: here we can do warning if retType is not tVoid and there is nothing to actually return
                      (\ a b -> Var returnFunc `Ap` a `Ap` b)
                      (Const $ returnName :>: toScheme retType)
                      returns
                )
              ]
            )
          ]
        , []
        )) >>= chmSchemize)
      leaveCHMHead
      leaveFunction
      return rtrn

instance Transform CStat where
  transform cStat = case cStat of
    CLabel _ stmt _ _ -> transform stmt
    CCase cExpr stmt _ -> do
      switchName <- getSwitchName
      anonNumber <- getNextAnon
      transExpr <- transformExpr cExpr
      transStmt <- transform stmt
      return $ ([],[[("@Case" ++ show anonNumber, [([],ap2 (Var caseFunc) (Var switchName) transExpr)])]]) : transStmt
    CCases lExpr rExpr stmt _ -> do  -- TODO: add checking for range-ness
      switchName <- getSwitchName
      anonNumber <- getNextAnon
      lTrans <- transformExpr lExpr
      rTrans <- transformExpr rExpr
      transStmt <- transform stmt
      return $ ([],[[("@Case" ++ show anonNumber, [([],ap2 (Var caseFunc) (Var switchName) lTrans), ([],ap2 (Var caseFunc) (Var switchName) rTrans)])]]) : transStmt
    CDefault stmt _ -> transform stmt
    CExpr (Just expr) _ -> transform expr
    CExpr Nothing _ -> return []
    CCompound _ [] _ -> return []
    CCompound _ block _ -> do
      enterScope []
      transBlock <- concat <$> traverse transform block
      leaveScope
      return transBlock
    CIf expr tStmt (Just fStmt) _ -> do
      anonNumber <- getNextAnon
      transExpr <- transformExpr expr
      tTrans <- transform tStmt
      fTrans <- transform fStmt
      return $ ([],[[("@IfElse" ++ show anonNumber, [([],transExpr)])]]) : (tTrans ++ fTrans)  -- TODO
    CIf expr tStmt Nothing _ -> do
      anonNumber <- getNextAnon
      transExpr <- transformExpr expr
      tTrans <- transform tStmt
      return $ ([],[[("@If" ++ show anonNumber, [([],transExpr)])]]) : tTrans  -- TODO
    CSwitch expr stmt _ -> do
      enterSwitch
      name <- getSwitchName
      transExpr <- transformExpr expr
      transStmt <- transform stmt
      leaveSwitch
      return $ ([],[[(name, [([],transExpr)])]]) : transStmt
    CWhile expr stmt _ _ -> do
      anonNumber <- getNextAnon
      transExpr <- transformExpr expr
      transStmt <- transform stmt
      return $ ([],[[("@While" ++ show anonNumber, [([],transExpr)])]]) : transStmt  -- TODO
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
  transT <- translateCHMType cType
  transTs <- traverse translateCHMType cTypes
  let
    apT = foldl TAp transT transTs
  fixKinds apT

transformConstraint :: CHMConstr -> TState (Maybe Pred)
transformConstraint constr =
  case constr of
    (CHMClassConstr (Ident id _ _) cTypes _) -> do
      let count = length cTypes
      transTypes <- traverse translateCHMType cTypes
      return . Just . IsIn id $ createParamsType transTypes
    (CHMUnifyConstr (Ident id _ _) cType _) -> do
      transType <- translateCHMType cType
      storeName id
      scopedName id >>= flip chmAddAlias transType
      return Nothing

translateConstraints :: [CHMConstr] -> TState ()
translateConstraints cs = sequence_
  [ do
    transC <- transformConstraint c
    case transC of
      Just x -> chmAddClass x
      _ -> return ()
  | c <- cs
  ]

instance Transform CHMHead where
  transform (CHMHead [] [] _) = return []
  transform (CHMHead types [] _) = sequence_
    [ do
      storeName id
      scopedId <- scopedName id
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
    transHead <- transform chmHead
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
    transHead <- transform chmHead
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
      fTrans <- transform f
      let [([(name, scheme, def)],[])] = fTrans
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
    transHead <- transform chmHead
    rtrn <- defineInstanceContents iId chmPars cExtDecls
    leaveCHMHead
    return [rtrn]
