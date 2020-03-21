{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
module CHM.Transform where

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
      Nothing -> ["programEnvironment" :>: toScheme tError]  -- TODO
      Just env -> tiProgram env bis program

collapse :: Program -> BindGroup
collapse ((expls, impls) : rest) =
  let
    (restExpls, restImpls) = collapse rest
  in (expls ++ restExpls, impls ++ restImpls)
collapse [] = ([],[])

toConst :: Type -> Type
toConst c@(TAp tConst a) = c
toConst c = TAp tConst c

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
  CTypeSpec (CSUType (CStruct CStructTag (Just (Ident sId _ _)) _ _ _) _) -> return $ TCon (Tycon sId Star)  -- TODO: same as TypeDef (just few rows below)
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
            transFirst <- translateDerivedDecl (translateDeclSpecs $ fst decl) (snd decl)
            transRest <- translatesDerivedDecl otherDecls
            return $ transFirst : transRest
          translatesDerivedDecl [] = return []
        in do
          types <- translatesDerivedDecl decls
          return $ foldl TAp (getTupleOp $ length types) types `fn` t'
      -- new-style functions (variadic)
      CFunDeclr (Right (decls, True)) _ _ -> return tError  -- TODO

extractParameters :: [CDecl] -> TState [Expl]
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
      scheme <- toScheme <$> translateDerivedDecl (translateDeclSpecs declSpecs) derived
      return $ (name, scheme, []) : others
extractParameters [] = return []


instance Transform CTranslUnit where
  transform (CTranslUnit [] _) = return []
  transform (CTranslUnit (extDecl:extDecls) a) = do
    decl <- transform extDecl
    decls <- transform (CTranslUnit extDecls a)
    return $ decl ++ decls

instance Transform CExtDecl where
  transform  (CDeclExt a)   = transform a
  transform  (CFDefExt a)   = transform a
  transform  (CHMFDefExt a) = transform a
  -- TODO: transform  (CHMSDefExt a) = transform a
  -- TODO: transform  (CHMCDefExt a) = transform a
  -- TODO: transform  (CHMIDefExt a) = transform a
  transform  (CAsmExt  a _) = transform a

-- these are better than the corresponding foldl because of the stronger type safety
ap2 :: Expr -> Expr -> Expr -> Expr
ap3 :: Expr -> Expr -> Expr -> Expr -> Expr

ap2 f a b = Ap (Ap f a) b
ap3 f a b c = Ap (Ap (Ap f a) b) c

    transforms [] = return []
    transforms (hExpr:tExprs) = do
      hTrans  <- transformExpr hExpr
      tTranss <- transforms tExprs
      return (hTrans:tTranss)
  in case cExpr of
  -- exprs is guaranteed to have at least 2 elements
  CComma exprs _ -> do
    transs <- transforms exprs
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
    return $ ap2
      (Var $ operatorFunction op)
      lTrans
      rTrans
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
    eTrans <- transforms exprs
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
    expr <- transformExpr cExpr
    return [([],[[("TODO", [([],expr)])]])]  -- TODO

instance Transform CFunDef where  -- TODO: make this and CHMFunDef use same bits of code
  transform (CFunDef specs (CDeclr (Just (Ident sId _ _)) derivedDecls _ _ _) decls stmt _) =
    let
      typeSignatures name fType = case head derivedDecls of
        -- old-style
        CFunDeclr (Left idents) _ _ ->
          return ([(name, toScheme fType, [])], [])  -- TODO
        -- not var-args
        CFunDeclr (Right (parDecls, False)) _ _ -> do
          pars <- extractParameters parDecls
          return ((name, toScheme fType, []) : pars, [])
        -- var-args
        CFunDeclr (Right (parDecls, True)) _ _ -> do
          pars <- extractParameters parDecls
          return ((name, toScheme fType, []) : pars, [])  -- TODO
        _ -> return ([(name, toScheme tError, [])],[])  -- TODO
    in do
      storeName sId
      name <- scopedName sId
      fType <- translateDerivedDecl (translateDeclSpecs specs) derivedDecls
      enterScope sId
      types <- typeSignatures name fType
      transStmt <- transform stmt
      leaveScope
      return $ types : transStmt

instance Transform CDecl where  -- TODO
  transform (CDecl specs declrs a) = case declrs of  -- TODO
    (Just (CDeclr (Just (Ident sId _ _)) derivedDecls _ _ _), Nothing, Nothing):rest -> do
      storeName sId
      name <- scopedName sId
      transType <- translateDerivedDecl (translateDeclSpecs specs) derivedDecls
      restTrans <- transform (CDecl specs rest a)
      return $ ([(name, toScheme transType, [])], []) : restTrans
    [] -> return []
  transform (CStaticAssert cExpr cStrLit _) = return []

instance Transform CStrLit where
  transform (CStrLit (CString s _) _) =
    return [([],[[("TODO", [([],Lit $ LitStr s)])]])]  -- TODO

instance Transform CHMFunDef where
  transform (CHMFunDef chmHead (CFunDef specs (CDeclr (Just (Ident sId _ _)) derivedDecls _ _ _) decls stmt _) _) =  -- TODO
    let
      typeSignatures name fType = case head derivedDecls of
        -- old-style
        CFunDeclr (Left idents) _ _ ->
          return ([(name, toScheme fType, [])], [])  -- TODO
        -- not var-args
        CFunDeclr (Right (parDecls, False)) _ _ -> do
          pars <- extractParameters parDecls
          return ((name, toScheme fType, []) : pars, [])
        -- var-args
        CFunDeclr (Right (parDecls, True)) _ _ -> do
          pars <- extractParameters parDecls
          return ((name, toScheme fType, []) : pars, [])  -- TODO
        _ -> return ([(name, toScheme tError, [])],[])  -- TODO
    in do
      storeName sId
      name <- scopedName sId
      fType <- translateDerivedDecl (translateDeclSpecs specs) derivedDecls
      enterScope sId
      types <- typeSignatures name fType
      transHead <- transform chmHead
      transStmt <- transform stmt
      leaveScope
      return $ transHead ++ types : transStmt

instance Transform CStat where
  transform cStat = case cStat of
    CLabel _ stmt _ _ -> transform stmt
    CCase cExpr stmt _ -> do
      name <- getSwitchName
      transExpr <- transformExpr cExpr
      transStmt <- transform stmt
      return $ ([],[[(name, [([],transExpr)])]]) : transStmt
    CCases lExpr rExpr stmt _ -> do  -- TODO: add checking for range-ness
      name <- getSwitchName
      lTrans <- transformExpr lExpr
      rTrans <- transformExpr rExpr
      transStmt <- transform stmt
      return $ ([],[[(name, [([],lTrans),([],rTrans)])]]) : transStmt
    CDefault stmt _ -> transform stmt
    CExpr (Just expr) _ -> transform expr
    CExpr Nothing _ -> return []
    CCompound _ [] _ -> return []
    CCompound _ block _ ->
      let
        transforms (first:rest) = do
          firstTrans <- transform first
          restTrans <- transforms rest
          return $ firstTrans ++ restTrans
        transforms [] = return []
      in do
        enterScope []
        transBlock <- transforms block
        leaveScope
        return transBlock
    CIf expr tStmt (Just fStmt) _ -> do
      transExpr <- transformExpr expr
      tTrans <- transform tStmt
      fTrans <- transform fStmt
      return $ ([],[[("TODO", [([],transExpr)])]]) : (tTrans ++ fTrans)  -- TODO
    CIf expr tStmt Nothing _ -> do
      transExpr <- transformExpr expr
      tTrans <- transform tStmt
      return $ ([],[[("TODO", [([],transExpr)])]]) : tTrans  -- TODO
    CSwitch expr stmt _ -> do
      enterSwitch
      name <- getSwitchName
      transExpr <- transformExpr expr
      transStmt <- transform stmt
      leaveSwitch
      return $ ([],[[(name, [([],transExpr)])]]) : transStmt
    CWhile expr stmt _ _ -> do
      transExpr <- transformExpr expr
      transStmt <- transform stmt
      return $ ([],[[("TODO", [([],transExpr)])]]) : transStmt  -- TODO
    CFor _ _ _ a _ -> return []  -- TODO
    CGoto _ _ -> return []
    CGotoPtr _ _ -> return []  -- TODO
    CCont _ ->  return []
    CBreak _ -> return []
    CReturn (Just a) _ -> return []  -- TODO: has to connect to the parent function
    CReturn Nothing _ -> return []  -- TODO: has to connect to the parent function
    CAsm _ _ -> return []

instance Transform CBlockItem where
  transform (CBlockStmt stmt) = transform stmt
  -- new variable
  transform (CBlockDecl cDecl) = transform cDecl
  transform (CNestedFunDef _) = return []  -- TODO: gnu thing, so maybe not-todo

instance Transform CHMHead where
  transform (CHMHead types constraints _) = return []  -- TODO
