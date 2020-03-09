{-# LANGUAGE TypeSynonymInstances, FlexibleInstances, FlexibleContexts #-}
module CHM.Transform where

import Data.Either

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
      foldl (++) [] [findReturn x | x <- block] -- TODO
    CIf _ a (Just b) _ -> findReturn a ++ findReturn b
    CIf _ a (Nothing) _ -> findReturn a
    CSwitch _ a _ -> findReturn a
    CWhile _ a _ _ -> findReturn a
    CFor _ _ _ a _ -> findReturn a
    CReturn _ _ -> -- finally
    CExpr _ _ -> []
    CGoto _ _ -> []
    CGotoPtr _ _ -> []
    CCont _ -> []
    CBreak _ -> []
    CAsm _ _ -> []

instance FindReturn CBlockItem where
  findReturn CBlockStmt -- TODO:
  findReturn CBlockDecl -- TODO:
  findReturn CNestedFunDef -- TODO:

instance Transform CFunDef where
  transform (CFunDef specs decl decls stmt _) =
    transform stmt
