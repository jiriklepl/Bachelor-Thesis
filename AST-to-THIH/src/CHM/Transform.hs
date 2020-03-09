{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
module CHM.Transform where

import TypingHaskellInHaskell
import Language.C.Data
import Language.C.Syntax

class Transform a where
  transform :: a -> [BindGroup]

instance Transform CTranslUnit where
  transform (CTranslUnit extDecls _) =
    foldl (++) [] [transform x | x <- extDecls]

instance Transform CExtDecl where
  transform  (CDeclExt a)   = transform a
  transform  (CFDefExt a)   = transform a
  transform  (CHMFDefExt a) = transform a
  transform  (CHMSDefExt a) = transform a
  transform  (CHMCDefExt a) = transform a
  transform  (CHMIDefExt a) = transform a
  transform  (CAsmExt  a _) = transform a

class FindReturn a where
  findReturn :: a -> [Expr]

instance FindReturn CStat where
  findReturn stmt = case stmt of
    CLabel _ a _ _ -> findReturn a
    CCase _ a _ -> findReturn a
    CCases _ _ a _ -> findReturn a
    CDefault a _ -> findReturn a
    CCompound _ block _ ->
      foldl (++) [] [findReturn x | x <- block]  -- TODO
    CIf _ a (Just b) _ -> findReturn a ++ findReturn b
    CIf _ a (Nothing) _ -> findReturn a
    CSwitch _ a _ -> findReturn a
    CWhile _ a _ _ -> findReturn a
    CFor _ _ _ a _ -> findReturn a
    CReturn (Nothing) _ -> [Var "()"]
    CReturn (Just a) _ ->
    CExpr _ _ -> []
    CGoto _ _ -> []
    CGotoPtr _ _ -> []
    CCont _ -> []
    CBreak _ -> []
    CAsm _ _ -> []

instance FindReturn CBlockItem where
  findReturn CBlockStmt  -- TODO:
  findReturn CBlockDecl  -- TODO:
  findReturn CNestedFunDef  -- TODO:

class OperatorFunction a where
  operatorFunction :: a -> Id

ternaryOpFunc :: Id
elvisOpFunc :: Id
indexOpFunc :: Id

instance Transform CExpr where
  -- the top-most binding should be first recursively (in comparison that would be the binding of ==, then operands and then their child bindings)
  transform cExpr = case CExpr of
    -- exprs is guaranteed to have at least 2 elements
    CComma exprs _ ->
      -- the very last (return-like) expression in the comma-separated list
      transform (last exprs) ++
      -- others
      foldl (++) [] [transform x | x <- init exprs]
    CAssign op lExpr rExpr _ ->
      [([],[[Ap $ Ap (Var $ operatorFunction op) lExpr rExpr]])] ++
      transform lExpr ++ -- should be l-expression (todo)
      transform rExpr
    -- this is the ternary operator
    CCond cExpr (Just tExpr) fExpr _ ->
      [([],[[Ap $ Ap (Var ternaryOpFunc) tExpr fExpr]])] ++
      transform tExpr ++
      transform eExpr
    -- this is elvis (supported by gnu)
    CCond cExpr (Nothing) fExpr ->
      [([],[[Ap (Var trinaryOpFunc) fExpr]])] ++
      transform fExpr
    CBinary op lExpr rExpr ->
      [([],[[Ap $ Ap (Var $ operatorFunction op) lExpr rExpr]])] ++
      transform lExpr ++
      transform rExpr
    -- TODO: CCast
    CUnary op expr ->
      [([],[[Ap (Var $ operatorFunction op) expr]])] ++
      transform expr
    -- TODO: CSizeofExpr
    -- TODO: CSizeofType
    -- ditto align
    -- TODO: CComplexReal
    CIndex aExpr iExpr ->
      [([],[[Ap $ Ap (Var indexOpFunc) lExpr rExpr]])] ++
      transform aExpr ++
      transform iExpr
    -- TODO

instance Transform CFunDef where
  transform (CFunDef specs decl decls stmt _) =
    transform stmt
