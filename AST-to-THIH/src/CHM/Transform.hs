{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
module CHM.Transform where

import TypingHaskellInHaskell
import Language.C.Data
import Language.C.Syntax
import Language.C.Data.Ident (Ident(..))

import CHM.TransformMonad

class Transform a where
  transform :: a -> TState [BindGroup]

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
  transform  (CHMSDefExt a) = transform a
  transform  (CHMCDefExt a) = transform a
  transform  (CHMIDefExt a) = transform a
  transform  (CAsmExt  a _) = transform a

class FindReturn a where
  findReturn :: a -> TState [Expr]

instance FindReturn CStat where
  findReturn stmt = case stmt of
    CLabel _ a _ _ -> findReturn a
    CCase _ a _ -> findReturn a
    CCases _ _ a _ -> findReturn a
    CDefault a _ -> findReturn a
    CCompound _ [] _ -> return []
    CCompound a (first:rest) b -> do
      firstReturn <- findReturn first
      otherReturns <- findReturn (CCompound a rest b)
      return (firstReturn ++ otherReturns)
    CIf _ a (Just b) _ -> do
      aReturn <- findReturn a
      bReturn <- findReturn b
      return (aReturn ++ bReturn)
    CIf _ a (Nothing) _ -> findReturn a
    CSwitch _ a _ -> findReturn a
    CWhile _ a _ _ -> findReturn a
    CFor _ _ _ a _ -> findReturn a
    CReturn (Nothing) _ -> return [Var "()"]
    CReturn (Just a) _ -> do
      expr <- transformExpr a
      return [expr]
    CExpr _ _ -> return []
    CGoto _ _ -> return []
    CGotoPtr _ _ -> return []
    CCont _ ->  return []
    CBreak _ -> return []
    CAsm _ _ -> return []

-- instance FindReturn CBlockItem where
--   findReturn CBlockStmt  -- TODO:
--   findReturn CBlockDecl  -- TODO:
--   findReturn CNestedFunDef  -- TODO:

transformExpr :: CExpr -> TState Expr
transformExpr cExpr = let
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
    transs <- (transforms exprs)
    return $ foldl1
      (\a b -> Ap (Ap (Var commaOpFunc) a) b)
      transs
  CAssign op lExpr rExpr _ -> do
    lTrans <- (transformExpr lExpr)
    rTrans <- (transformExpr rExpr)
    return $ ap2
      (Var $ operatorFunction op)
      lTrans
      rTrans
  -- this is the ternary operator
  CCond cExpr (Just tExpr) fExpr _ -> do
    cTrans <- (transformExpr tExpr)
    tTrans <- (transformExpr tExpr)
    fTrans <- (transformExpr fExpr)
    return $ ap3
      (Var ternaryOpFunc)
      cTrans
      tTrans
      fTrans
  -- this is elvis (supported by gnu)
  CCond cExpr (Nothing) fExpr _ -> do
    cTrans <- (transformExpr cExpr)
    fTrans <- (transformExpr fExpr)
    return $ ap2
      (Var elvisOpFunc)
      cTrans
      fTrans
  CBinary op lExpr rExpr _ -> do
    lTrans <- (transformExpr lExpr)
    rTrans <- (transformExpr rExpr)
    return $ ap2
      (Var $ operatorFunction op)
      lTrans
      rTrans
  -- TODO: CCast
  CUnary op expr _ -> do
    trans <- (transformExpr expr)
    return $ Ap
      (Var $ operatorFunction op)
      trans
  -- TODO: CSizeofExpr
  -- TODO: CSizeofType
  -- ditto align
  -- TODO: CComplexReal
  CIndex aExpr iExpr _ -> do
    aTrans <- (transformExpr aExpr)
    iTrans <- (transformExpr iExpr)
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
  CMember sExpr mId true  _ -> do
    member <- (getMember mId)
    sTrans <- transformExpr sExpr
    return $ Ap
      (Var member)
      (deref sTrans)
  -- sExpr.mId
  CMember sExpr mId false  _ -> do
    member <- (getMember mId)
    sTrans <- transformExpr sExpr
    return $ Ap
      (Var member)
      sTrans
  CVar (Ident sId _ _) _ ->
    return $ Var sId
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

instance Transform CFunDef where
  transform (CFunDef specs decl decls stmt _) =
    transform stmt  -- TODO

instance Transform CDecl where  -- TODO
  transform (CDecl cDeclSpecs cDecls _) = return []
  transform (CStaticAssert cExpr cStrLit _) = return []

instance Transform CStrLit where
  transform (CStrLit (CString s _) _) =
    return [([],[[("TODO", [([],Lit $ LitStr s)])]])]  -- TODO

instance Transform CHMFunDef where
  transform (CHMFunDef head funDef _) = do
    tHead <- transform head
    tFunDef <- transform funDef
    -- here we should rename the variables, the best for that would be a nest variable in the monad
    return $ tHead ++ tFunDef
