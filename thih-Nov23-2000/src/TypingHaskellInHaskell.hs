-----------------------------------------------------------------------------
-- | Thih:		Typing Haskell in Haskell, main program
--
-- Part of `Typing Haskell in Haskell', version of November 23, 2000
-- Copyright (c) Mark P Jones and the Oregon Graduate Institute
-- of Science and Technology, 1999-2000
--
-- This program is distributed as Free Software under the terms
-- in the file "License" that is included in the distribution
-- of this software, copies of which may be obtained from:
--             http://www.cse.ogi.edu/~mpj/thih/
--
--
-- This file contains all the text from the paper in one single file
-- that can be loaded into Hugs for type checking.  No additional code
-- is included.
--
-- Like other incarnations of this program, this version is generated
-- automatically from the very same source code as the others.  Its
-- *sole* purpose in life is to provide a quick way to check that the
-- code in the paper is free from syntax and type errors.  If you
-- actually want to run the program with real data, use the multiple
-- file version.
--
-----------------------------------------------------------------------------

module TypingHaskellInHaskell where

import Data.Foldable hiding (find)
import Data.List (partition, (\\))
import qualified Data.Set as Set
import qualified Data.Map as Map

import qualified Data.ByteString.Char8 as T

import Control.Monad
import qualified Control.Monad.Fail as Fail

import Control.Applicative(Applicative(..))

-----------------------------------------------------------------------------
-- Id:		Identifiers
-----------------------------------------------------------------------------

type Id  = T.ByteString

enumId  :: Int -> Id
enumId n = 'v' `T.cons` T.pack (show n)

-----------------------------------------------------------------------------
-- Kind:		Kinds
-----------------------------------------------------------------------------

data Kind  = Star | Kfun Kind Kind
             deriving (Eq, Show, Ord)

-----------------------------------------------------------------------------
-- Type:		Types
-----------------------------------------------------------------------------

data Type  = TVar Tyvar | TCon Tycon | TAp Type Type | TGen Int
             deriving (Eq, Show, Ord)

data Tyvar = Tyvar Id Kind
             deriving (Eq, Show)

instance Ord Tyvar where
  compare (Tyvar id1 _) (Tyvar id2 _) = compare id1 id2

data Tycon = Tycon Id Kind
             deriving (Eq, Show)

instance Ord Tycon where
  compare (Tycon id1 _) (Tycon id2 _) = compare id1 id2

tCharId   = T.pack "Char"
tIntId    = T.pack "Int"
tFloatId  = T.pack "Float"
tDoubleId = T.pack "Double"

tListId   = T.pack "[]"
tArrowId  = T.pack "(->)"
tTuple2Id = T.pack "(,)2"

cNumId    = T.pack "Num"

-- CHM additions
tErrorId = T.pack "@Error"
tVoidId = T.pack "Void"
tShortId = T.pack "Short"
tLongId = T.pack "Long"
tLongSpecId = T.pack "LongSpec"
tSignedId = T.pack "Signed"
tUnsigId = T.pack "Unsig"
tBoolId = T.pack "Bool"
tComplexId = T.pack "Complex"
tInt128Id = T.pack "Int128"

tUnit    = TCon (Tycon (T.pack "()") Star)
tChar    = TCon (Tycon tCharId Star)
tInt     = TCon (Tycon tIntId Star)
tFloat   = TCon (Tycon tFloatId Star)
tDouble  = TCon (Tycon tDoubleId Star)

-- CHM additions
tError  = TCon (Tycon tErrorId Star)
tVoid  = TCon (Tycon tVoidId Star)
tShort = TCon (Tycon tShortId Star)
tLong = TCon (Tycon tLongId Star)
tLongSpec = TCon (Tycon  tLongSpecId(Kfun Star Star))
tSigned = TCon (Tycon tSignedId Star)
tUnsig = TCon (Tycon tUnsigId Star)
tBool = TCon (Tycon tBoolId Star)
tComplex = TCon (Tycon tComplexId Star)
tInt128 = TCon (Tycon tInt128Id Star)

tList    = TCon (Tycon tListId (Kfun Star Star))
tArrow   = TCon (Tycon tArrowId (Kfun Star (Kfun Star Star)))
tTuple2  = TCon (Tycon tTuple2Id (Kfun Star (Kfun Star Star)))

tString    :: Type
tString     = list tChar

infixr      4 `fn`
fn         :: Type -> Type -> Type
a `fn` b    = TAp (TAp tArrow a) b

list       :: Type -> Type
list        = (tList `TAp`)

pair       :: Type -> Type -> Type
pair        = TAp . TAp tTuple2

class HasKind t where
  kind :: t -> Kind
instance HasKind Tyvar where
  kind (Tyvar v k) = k
instance HasKind Tycon where
  kind (Tycon v k) = k
instance HasKind Type where
  kind (TCon tc) = kind tc
  kind (TVar u)  = kind u
  kind (TAp t _) = case kind t of
                     Kfun _ k -> k

-----------------------------------------------------------------------------
-- Subst:	Substitutions
-----------------------------------------------------------------------------

type Subst  = Map.Map Tyvar Type

nullSubst  :: Subst
nullSubst   = Map.empty

(+->)      :: Tyvar -> Type -> Subst
u +-> t     = Map.singleton u t

class Types t where
  apply :: Subst -> t -> t
  tv    :: t -> Set.Set Tyvar

instance Types Type where
  apply s (TVar u)  = case Map.lookup u s of
                       Just t  -> t
                       Nothing -> TVar u
  apply s (TAp l r) = TAp (apply s l) (apply s r)
  apply s t         = t

  tv (TVar u)  = Set.singleton u
  tv (TAp l r) = tv l `Set.union` tv r
  tv t         = Set.empty

instance Types a => Types [a] where
  apply s = map (apply s)
  tv      = Set.unions . map tv

instance (Ord a, Types b) => Types (Map.Map a b) where
  apply s = Map.map (apply s)
  tv      = foldl' ( (. tv) . Set.union) Set.empty

infixr 4 @@
(@@)       :: Subst -> Subst -> Subst
s1 @@ s2    = Map.map (apply s1) s2 `Map.union` s1

merge      :: Fail.MonadFail m => Subst -> Subst -> m Subst
merge s1 s2 = if agree then return (s1 `Map.union` s2) else fail "merge fails"
 where agree = all (\v -> apply s1 (TVar v) == apply s2 (TVar v))
                   (Map.keysSet s1 `Set.intersection` Map.keysSet s2)

-----------------------------------------------------------------------------
-- Unify:	Unification
-----------------------------------------------------------------------------

mgu     :: Fail.MonadFail m => Type -> Type -> m Subst
varBind :: Fail.MonadFail m => Tyvar -> Type -> m Subst

mgu (TAp l r) (TAp l' r') = do s1 <- mgu l l'
                               s2 <- mgu (apply s1 r) (apply s1 r')
                               return (s2 @@ s1)
mgu (TVar u) t        = varBind u t
mgu t (TVar u)        = varBind u t
mgu (TCon tc1) (TCon tc2)
           | tc1==tc2 = return nullSubst
mgu t1 t2             = fail $ "types `" ++ show t1 ++ "` and `" ++ show t2 ++ "` do not unify"

varBind u t | t == TVar u      = return nullSubst
            | u `elem` tv t    = fail "occurs check fails"
            | kind u /= kind t = fail $ "kinds of `" ++ show u ++ "` and `" ++ show t ++ "` do not match"
            | otherwise        = return (u +-> t)

match :: Fail.MonadFail m => Type -> Type -> m Subst

match (TAp l r) (TAp l' r') = do sl <- match l l'
                                 sr <- match r r'
                                 merge sl sr
match (TVar u)   t | kind u == kind t = return (u +-> t)
match (TCon tc1) (TCon tc2)
         | tc1==tc2         = return nullSubst
match t1 t2                 = fail "types do not match"

-----------------------------------------------------------------------------
-- Pred:		Predicates
-----------------------------------------------------------------------------

data Qual t = [Pred] :=> t
              deriving (Eq, Show)

data Pred   = IsIn Id Type
              deriving (Eq, Show)

instance Types t => Types (Qual t) where
  apply s (ps :=> t) = apply s ps :=> apply s t
  tv (ps :=> t)      = tv ps `Set.union` tv t

instance Types Pred where
  apply s (IsIn i t) = IsIn i (apply s t)
  tv (IsIn i t)      = tv t

mguPred, matchPred :: Pred -> Pred -> Maybe Subst
mguPred             = lift mgu
matchPred           = lift match

lift m (IsIn i t) (IsIn i' t')
         | i == i'   = m t t'
         | otherwise = fail "classes differ"

type Class    = ([Id], [Inst])
type Inst     = Qual Pred

-----------------------------------------------------------------------------

data ClassEnv = ClassEnv { classes  :: Id -> Maybe Class,
                           defaults :: [Type] }

super     :: ClassEnv -> Id -> [Id]
super ce i = case classes ce i of Just (is, its) -> is

insts     :: ClassEnv -> Id -> [Inst]
insts ce i = case classes ce i of Just (is, its) -> its

defined :: Maybe a -> Bool
defined (Just x) = True
defined Nothing  = False

modify       :: ClassEnv -> Id -> Class -> ClassEnv
modify ce i c = ce{classes = \j -> if i==j then Just c
                                           else classes ce j}

initialEnv :: ClassEnv
initialEnv  = ClassEnv { classes  = const $ fail "class not defined",
                         defaults = [tInt, tDouble] }

type EnvTransformer = ClassEnv -> Maybe ClassEnv

infixr 5 <:>
(<:>)       :: EnvTransformer -> EnvTransformer -> EnvTransformer
(f <:> g) ce = do ce' <- f ce
                  g ce'

addClass                              :: Id -> [Id] -> EnvTransformer
addClass i is ce
 | defined (classes ce i)              = fail "class already defined"
 | not (all (defined . classes ce) is) = fail "superclass not defined"
 | otherwise                           = return (modify ce i (is, []))

addInst                        :: [Pred] -> Pred -> EnvTransformer
addInst ps p@(IsIn i _) ce
 | not (defined (classes ce i)) = fail "no class for instance"
 | any (overlap p) qs           = fail "overlapping instance"
 | otherwise                    = return (modify ce i c)
   where its = insts ce i
         qs  = [ q | (_ :=> q) <- its ]
         c   = (super ce i, (ps:=>p) : its)

overlap       :: Pred -> Pred -> Bool
overlap p q    = defined (mguPred p q)

-----------------------------------------------------------------------------

bySuper :: ClassEnv -> Pred -> [Pred]
bySuper ce p@(IsIn i t)
 = p : concat [ bySuper ce (IsIn i' t) | i' <- super ce i ]

byInst                   :: ClassEnv -> Pred -> Maybe [Pred]
byInst ce p@(IsIn i t)    = msum [ tryInst it | it <- insts ce i ]
 where tryInst (ps :=> h) = do u <- matchPred h p
                               Just (map (apply u) ps)

entail        :: ClassEnv -> [Pred] -> Pred -> Bool
entail ce ps p = any ((p `elem`) . bySuper ce) ps ||
                 case byInst ce p of
                   Nothing -> False
                   Just qs -> all (entail ce ps) qs

-----------------------------------------------------------------------------

inHnf       :: Pred -> Bool
inHnf (IsIn c t) = hnf t
 where hnf (TVar v)  = True
       hnf (TCon tc) = False
       hnf (TAp t _) = hnf t

toHnfs      :: Fail.MonadFail m => ClassEnv -> [Pred] -> m [Pred]
toHnfs ce ps = do pss <- mapM (toHnf ce) ps
                  return (concat pss)

toHnf                 :: Fail.MonadFail m => ClassEnv -> Pred -> m [Pred]
toHnf ce p | inHnf p   = return [p]
           | otherwise = case byInst ce p of
                           Nothing -> fail "context reduction"
                           Just ps -> toHnfs ce ps

simplify   :: ClassEnv -> [Pred] -> [Pred]
simplify ce = loop []
 where loop rs []                            = rs
       loop rs (p:ps) | entail ce (rs++ps) p = loop rs ps
                      | otherwise            = loop (p:rs) ps

reduce      :: Fail.MonadFail m => ClassEnv -> [Pred] -> m [Pred]
reduce ce ps = do qs <- toHnfs ce ps
                  return (simplify ce qs)

scEntail        :: ClassEnv -> [Pred] -> Pred -> Bool
scEntail ce ps p = any ((p `elem`) . bySuper ce) ps

-----------------------------------------------------------------------------
-- Scheme:	Type schemes
-----------------------------------------------------------------------------

data Scheme = Forall [Kind] (Qual Type)
              deriving (Eq, Show)

instance Types Scheme where
  apply s (Forall ks qt) = Forall ks (apply s qt)
  tv (Forall ks qt)      = tv qt

quantify      :: Set.Set Tyvar -> Qual Type -> Scheme
quantify vs qt = Forall ks (apply s qt)
 where vs' = Set.filter (`elem` vs) (tv qt)
       vs'' = Set.toList vs'
       ks  = map kind vs''
       s   = Map.fromList $ zip (vs'') (map TGen [0..])

toScheme      :: Type -> Scheme
toScheme t     = Forall [] ([] :=> t)

-----------------------------------------------------------------------------
-- Assump:	Assumptions
-----------------------------------------------------------------------------

data Assump = Id :>: Scheme deriving(Show, Eq)

instance Types Assump where
  apply s (i :>: sc) = i :>: apply s sc
  tv (i :>: sc)      = tv sc

instance Ord Assump where
  compare (id1 :>: _) (id2 :>: _) = compare id1 id2

find :: Fail.MonadFail m => Id -> Map.Map Id Scheme -> m Scheme
find i as = let errorMSG = fail ("unbound identifier: " ++ T.unpack i)
  in case i `Map.lookup` as of
    Just sc -> return sc
    Nothing -> errorMSG

-----------------------------------------------------------------------------
-- TIMonad:	Type inference monad
-----------------------------------------------------------------------------

newtype TI a = TI (Subst -> Int -> (Subst, Int, a))

instance Fail.MonadFail TI where
  fail = error

instance Monad TI where
  return x   = TI (\s n -> (s,n,x))
  TI f >>= g = TI (\s n -> case f s n of
                            (s',m,x) -> let TI gx = g x
                                        in  gx s' m)

instance Applicative TI where
  pure                   = return
  liftA2 f (TI g) (TI h) = TI (\s n -> let (s', n', x) = g s n
                                           (s'', n'', y) = h s' n'
                                       in (s'', n'', f x y))

instance Functor TI where
  fmap f xs = f <$> xs

runTI       :: TI a -> a
runTI (TI f) = x where (s,n,x) = f nullSubst 0

getSubst   :: TI Subst
getSubst    = TI (\s n -> (s,n,s))

unify      :: Type -> Type -> TI ()
unify t1 t2 = do s <- getSubst
                 u <- mgu (apply s t1) (apply s t2)
                 extSubst u

extSubst   :: Subst -> TI ()
extSubst s' = TI (\s n -> (s' @@ s, n, ()))

newTVar    :: Kind -> TI Type
newTVar k   = TI (\s n -> let v = Tyvar (enumId n) k
                          in  (s, n+1, TVar v))

freshInst               :: Scheme -> TI (Qual Type)
freshInst (Forall ks qt) = do ts <- mapM newTVar ks
                              return (inst ts qt)

class Instantiate t where
  inst  :: [Type] -> t -> t
instance Instantiate Type where
  inst ts (TAp l r) = TAp (inst ts l) (inst ts r)
  inst ts (TGen n)  = ts !! n
  inst ts t         = t
instance Instantiate a => Instantiate [a] where
  inst ts = map (inst ts)
instance Instantiate t => Instantiate (Qual t) where
  inst ts (ps :=> t) = inst ts ps :=> inst ts t
instance Instantiate Pred where
  inst ts (IsIn c t) = IsIn c (inst ts t)

-----------------------------------------------------------------------------
-- TIMain:	Type Inference Algorithm
-----------------------------------------------------------------------------
-- Infer:	Basic definitions for type inference
-----------------------------------------------------------------------------

type Infer e t = ClassEnv -> Map.Map Id Scheme -> e -> TI ([Pred], t)

-----------------------------------------------------------------------------
-- Lit:		Literals
-----------------------------------------------------------------------------

data Literal = LitInt  Integer
             | LitChar Char
             | LitFloat String  -- (CHM) added like this to mirror the Language.C definition
             | LitStr  String
             | LitVoid
             deriving(Show)

tiLit            :: Literal -> TI ([Pred],Type)
tiLit (LitChar _) = return ([], tChar)
tiLit (LitInt _)  = do v <- newTVar Star
                       return ([IsIn cNumId v], v)
tiLit (LitStr _)  = return ([], tString)
tiLit (LitFloat _)  = return ([], tFloat)  -- (CHM)
tiLit LitVoid  = return ([], tVoid)  -- (CHM)

-----------------------------------------------------------------------------
-- Pat:		Patterns
-----------------------------------------------------------------------------

data Pat        = PVar Id
                | PCon Assump [Pat]
                deriving(Show)

tiPat :: Pat -> TI ([Pred], Map.Map Id Scheme, Type)

tiPat (PVar i) = do v <- newTVar Star
                    return ([], Map.singleton i $ toScheme v, v)

tiPat (PCon (i:>:sc) pats) = do (ps,as,ts) <- tiPats pats
                                t'         <- newTVar Star
                                (qs :=> t) <- freshInst sc
                                unify t (foldr' fn t' ts)
                                return (ps++qs, as, t')

tiPats     :: [Pat] -> TI ([Pred], Map.Map Id Scheme, [Type])
tiPats pats = do
  psasts <- mapM tiPat pats
  let
    ps = concat [ps' | (ps',_,_) <- psasts]
    as = Map.unions [as' | (_,as',_) <- psasts]
    ts = [t | (_,_,t) <- psasts]
  return (ps, as, ts)

-----------------------------------------------------------------------------

data Expr = Var   Id
          | Lit   Literal
          | Const Assump
          | Ap    Expr Expr
          | Let   BindGroup Expr
          | Lambda Alt
          | LambdaScheme Scheme Alt
          deriving(Show)

tiExpr                       :: Infer Expr Type
tiExpr ce as (Var i)          = do sc         <- find i as
                                   (ps :=> t) <- freshInst sc
                                   return (ps, t)
tiExpr ce as (Const (i:>:sc)) = do (ps :=> t) <- freshInst sc
                                   return (ps, t)
tiExpr ce as (Lit l)          = do (ps,t) <- tiLit l
                                   return (ps, t)
tiExpr ce as (Ap e f)         = do (ps,te) <- tiExpr ce as e
                                   (qs,tf) <- tiExpr ce as f
                                   t       <- newTVar Star
                                   unify (tf `fn` t) te
                                   return (ps ++ qs, t)
tiExpr ce as (Let bg e)       = do (ps, as') <- tiBindGroup ce as bg
                                   (qs, t)   <- tiExpr ce (as' `Map.union` as) e
                                   return (ps ++ qs, t)

tiExpr ce as (Lambda alt)          = tiAlt ce as alt
tiExpr ce as (LambdaScheme sc alt) = do (qs :=> te) <- freshInst sc
                                        (ps, tf) <- tiAlt ce as alt
                                        unify te tf
                                        return (ps ++ qs, te)


-----------------------------------------------------------------------------

type Alt = ([Pat], Expr)

tiAlt                :: Infer Alt Type
tiAlt ce as (pats, e) = do (ps, as', ts) <- tiPats pats
                           (qs,t)  <- tiExpr ce (as' `Map.union` as) e
                           return (ps++qs, foldr' fn t ts)

tiAlts             :: ClassEnv -> Map.Map Id Scheme -> [Alt] -> Type -> TI [Pred]
tiAlts ce as alts t = do psts <- mapM (tiAlt ce as) alts
                         mapM_ (unify t . snd) psts
                         return (concatMap fst psts)

-----------------------------------------------------------------------------

split :: Fail.MonadFail m => ClassEnv -> Set.Set Tyvar -> Set.Set Tyvar -> [Pred]
                      -> m ([Pred], [Pred])
split ce fs gs ps = do ps' <- reduce ce ps
                       let (ds, rs) = partition (all (`elem` fs) . tv) ps'
                       rs' <- defaultedPreds ce (fs `Set.union` gs) rs
                       return (ds, rs \\ rs')

type Ambiguity       = (Tyvar, [Pred])

ambiguities         :: ClassEnv -> Set.Set Tyvar -> [Pred] -> [Ambiguity]
ambiguities ce vs ps = [ (v, filter (elem v . tv) ps) | v <- Set.toList $ tv ps Set.\\ vs ]

numClasses :: [Id]
numClasses  = T.pack <$> ["Num", "Integral", "Floating", "Fractional",
               "Real", "RealFloat", "RealFrac"]

stdClasses :: [Id]
stdClasses  = (T.pack <$> ["Eq", "Ord", "Show", "Read", "Bounded", "Enum", "Ix",
               "Functor", "Monad", "MonadPlus"]) ++ numClasses

candidates           :: ClassEnv -> Ambiguity -> [Type]
candidates ce (v, qs) = [ t' | let is = [ i | IsIn i t <- qs ]
                                   ts = [ t | IsIn i t <- qs ],
                               all (TVar v ==) ts,
                               any (`elem` numClasses) is,
                               all (`elem` stdClasses) is,
                               t' <- defaults ce,
                               all (entail ce []) [ IsIn i t' | i <- is ] ]

withDefaults :: Fail.MonadFail m => ([Ambiguity] -> [Type] -> a)
                  -> ClassEnv -> Set.Set Tyvar -> [Pred] -> m a
withDefaults f ce vs ps
    | any null tss  = fail "cannot resolve ambiguity"
    | otherwise     = return (f vps (map head tss))
      where vps = ambiguities ce vs ps
            tss = map (candidates ce) vps

defaultedPreds :: Fail.MonadFail m => ClassEnv -> Set.Set Tyvar -> [Pred] -> m [Pred]
defaultedPreds  = withDefaults (const . concatMap snd)

defaultSubst   :: Fail.MonadFail m => ClassEnv -> Set.Set Tyvar -> [Pred] -> m Subst
defaultSubst    = withDefaults (\a b -> Map.fromList $ zip (map fst a) b)

-----------------------------------------------------------------------------

type Expl = (Id, Scheme, [Alt])

tiExpl :: ClassEnv -> Map.Map Id Scheme -> Expl -> TI [Pred]
tiExpl ce as (i, sc, alts)
        = do (qs :=> t) <- freshInst sc
             ps         <- tiAlts ce as alts t
             s          <- getSubst
             let qs'     = apply s qs
                 t'      = apply s t
                 fs      = tv (apply s as)
                 gs      = tv t' Set.\\ fs
                 sc'     = quantify gs (qs':=>t')
                 ps'     = filter (not . entail ce qs') (apply s ps)
             (ds,rs)    <- split ce fs gs ps'
             if sc /= sc' then
                 fail $
                    "signature `" ++ show sc ++
                    "` of `" ++ show i ++
                    "` incompatible with `" ++ show sc' ++ "`"
               else if not (null rs) then
                 fail "context too weak"
               else
                 return ds

-----------------------------------------------------------------------------

type Impl   = (Id, [Alt])

restricted   :: [Impl] -> Bool
restricted = any simple
 where simple (i,alts) = any (null . fst) alts

tiImpls         :: Infer [Impl] (Map.Map Id Scheme)
tiImpls ce as bs = do ts <- sequence $ take (length bs) [newTVar Star]
                      let zIs = Map.fromList . zip is
                          is    = map fst bs
                          scs   = map toScheme ts
                          as'   = zIs scs `Map.union` as
                          altss = map snd bs
                      pss <- zipWithM (tiAlts ce as') altss ts
                      s   <- getSubst
                      let ps'     = apply s (concat pss)
                          ts'     = apply s ts
                          fs      = tv (apply s as)
                          vss     = map tv ts'
                          gs      = Set.unions vss Set.\\ fs
                      (ds,rs) <- split ce fs (foldl1 Set.intersection vss) ps'
                      if restricted bs then
                          let gs'  = gs Set.\\ tv rs
                              scs' = map (quantify gs' . ([]:=>)) ts'
                          in return (ds++rs, zIs scs')
                        else
                          let scs' = map (quantify gs . (rs:=>)) ts'
                          in return (ds, zIs scs')

-----------------------------------------------------------------------------

type BindGroup  = ([Expl], [[Impl]])

tiBindGroup :: Infer BindGroup (Map.Map Id Scheme)
tiBindGroup ce as (es,iss) =
  do let as' = Map.fromList [ (v,sc) | (v,sc,alts) <- es ]
     (ps, as'') <- tiSeq tiImpls ce (as' `Map.union` as) iss
     qss        <- mapM (tiExpl ce (as'' `Map.union` as' `Map.union` as)) es
     return (ps++concat qss, as'' `Map.union` as')

tiSeq                  :: Infer bg (Map.Map Id Scheme) -> Infer [bg] (Map.Map Id Scheme)
tiSeq ti ce as []       = return ([],Map.empty)
tiSeq ti ce as (bs:bss) = do (ps,as')  <- ti ce as bs
                             (qs,as'') <- tiSeq ti ce (as' `Map.union` as) bss
                             return (ps ++ qs, as'' `Map.union` as')

-----------------------------------------------------------------------------
-- TIProg:	Type Inference for Whole Programs
-----------------------------------------------------------------------------

type Program = [BindGroup]

tiProgram :: ClassEnv -> Map.Map Id Scheme -> Program -> Map.Map Id Scheme
tiProgram ce as bgs = runTI $
                      do (ps, as') <- tiSeq tiBindGroup ce as bgs
                         s         <- getSubst
                         rs        <- reduce ce (apply s ps)
                         s'        <- defaultSubst ce Set.empty rs
                         return (apply (s' @@ s) as')

-----------------------------------------------------------------------------
