{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
module CHM.Transform where

import TypingHaskellInHaskell
import Language.C.Data
import Language.C.Syntax

import CHM.TransformMonad

class Transform a where
  transform :: a -> TState [BindGroup]

instance Transform CTranslUnit where
  transform (CTranslUnit [] _) = return []
  transform (CTranslUnit (extDecl:extDecls) _) = do
    decl <- transform extDecl
    decls <- transform extDecls
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

class OperatorFunction a where
  operatorFunction :: a -> Id

commaOpFunc   :: Id  -- takes two things and returns the second
ternaryOpFunc :: Id
elvisOpFunc   :: Id
indexOpFunc   :: Id

commaOpFunc   = ","
ternaryOpFunc = ":?"
elvisOpFunc   = ":?"
indexOpFunc   = "[]"

transformExpr :: CExpr -> TState Expr
transformExpr cExpr = let
    ap2 f a b = Ap (Ap f a) b
    ap3 f a b c = Ap (Ap (Ap f a) b)
  in case CExpr of
  -- exprs is guaranteed to have at least 2 elements
  CComma exprs _ ->
    return $ foldl1
      (\a b -> Ap (Ap (Var "commaOpFunc") a) b)
      (transformExpr <$> exprs)
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
  CCond cExpr (Nothing) fExpr _ ->
    return $ ap2
      (Var elvisOpFunc)  -- TODO from here...
      (transformExpr cExpr)
      (transformExpr fExpr)
  CBinary op lExpr rExpr _ ->
    return $ ap2
      (Var $ operatorFunction op)
      (transformExpr lExpr)
      (transformExpr rExpr)
  -- TODO: CCast
  CUnary op expr _ ->
    return $ Ap
      (Var $ operatorFunction op)
      (transform expr)
  -- TODO: CSizeofExpr
  -- TODO: CSizeofType
  -- ditto align
  -- TODO: CComplexReal
  CIndex aExpr iExpr _ ->
    return $ ap2
      (Var indexOpFunc)
      (transformExpr aExpr)
      (transformExpr iExpr)
  CCall func exprs _ -> do
    tuple <- getTuple (length exprs)
    return $ Ap
      (transform func)
      (foldl Ap (Var tuple) (transform <$> exprs))

instance Transform CExpr where
  -- the top-most binding should be first recursively (in comparison that would be the binding of ==, then operands and then their child bindings)
  transform cExpr = do
    expr <- transformExpr cExpr
    return [([],[[("TODO", [([],expr)])]])] -- TODO

instance Transform CFunDef where
  transform (CFunDef specs decl decls stmt _) =
    transform stmt
