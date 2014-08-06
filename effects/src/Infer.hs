{-# LANGUAGE ParallelListComp #-}

module Infer where

import           Control.Applicative ( (<$>) )

import           Data.Foldable ( toList )
import           Data.Map.Strict ( Map )
import qualified Data.Map as Map
import           Data.Set ( Set )
import qualified Data.Set as Set

import           Subst ( Subst, SubstTarget(..), (++.) )
import qualified Subst
import           Syntax
import           Unify ( unify )
import           Unique ( Unique )
import qualified Unique as Uniq

-------------------------------------------------
-- * Type Inferece

infer :: Env -> Exp -> TI ({-Subst,-}Type,Effect,Constraints)
infer env e = do
  (theta,ty,ef,k) <- infer' env e
  return ({-theta,-}ty,cobserve k (theta$.env) ty ef,k)

infer' :: Env -> Exp -> TI (Subst,Type,Effect,Constraints)
infer' env (Var x)
  | Just (CForallTy as ty k) <- lookupVar env x
  = do bs <- freshVars as
       let u = Subst.fromList [ (a,VarTy b) | a <- as | b <- bs ]
       return (Subst.id,u$.ty,EmptyEff,u$.k)
  | otherwise
  = error "infer': variable not found"
infer' env (Lam x e) = do
  a <- freshVarTy
  l <- freshVar EffKind
  (theta,ty,eff,k) <- infer' (extendEnv x (CForallTy [] a []) env) e
  return (theta,FunTy (theta$.a) (VarEff l) ty,EmptyEff,l :>= eff : k)
infer' env (Let x e e') = do
  (theta,ty,ef,k) <- infer' env e
  let env1 = theta$.env
      env' = extendEnv x (cgen k ef env1 ty) env1
  (theta',ty',ef',k') <- infer' env' e'
  return (theta'++.theta,ty',(theta'$.ef) :+ ef',(theta'$.k) ++ k')
infer' env (App e e') = do
  (theta,ty,ef,k) <- infer' env e
  (theta',ty',ef',k') <- infer' (theta$.env) e'
  a <- freshVarTy
  ee <- freshVarEff
  let theta'' = (theta'$.ty) `unify` FunTy ty' ee a
      theta1  = theta''++.theta'++.theta
      ty1     = theta''$.a
      ef1     = theta''$.((theta'$.ef) :+ ef' :+ ee)
      k1      = theta''$.(theta'$.k ++ k')
  return (theta1,ty1,ef1,k1)

-------------------------------------------------
-- * Type Inferece (TI) Monad

type TI = Unique

freshVar :: Kind -> TI TyVar
freshVar ki = TyVar ki <$> Uniq.getUniq

freshVars :: TyVars -> TI TyVars
freshVars as = mapM freshVar (map tvKind as)

freshVarTy :: TI Type
freshVarTy = VarTy <$> freshVar TypKind

freshVarEff :: TI Effect
freshVarEff = VarEff <$> freshVar EffKind

-------------------------------------------------
-- * Typing Environment

data Env = Env { unEnv :: !(Map Var CSig) }

lookupVar :: Env -> Var -> Maybe CSig
lookupVar (Env m) v = Map.lookup v m

extendEnv :: Var -> CSig -> Env -> Env
extendEnv v t = Env . Map.insert v t . unEnv

instance FV Env where
  fv = Set.unions . map fv . Map.elems . unEnv

instance FR Env where
  fr = Set.unions . map fr . Map.elems . unEnv

instance SubstTarget Env where
  u $. (Env m) = Env $ fmap (u $.) m

-------------------------------------------------
-- * Type Generalization

gen :: Effect -> Env -> Type -> Sig
gen oEff env ty = ForallTy vars ty
  where vars = toList $ fv ty Set.\\ (fv env `Set.union` fv oEff)

-------------------------------------------------
-- * Observable Effects

observe :: Env -> Type -> Effect -> Effect
observe env ty eff = sumEff $
     [ VarEff x | x <- toList $ effectVars eff
                , x `Set.member` observableEffectVars
                ]
  ++ [ se | se <- toList $ storeEffects eff
          , storeRegion se `Set.member` observableRegions
          ]
  where observableEffectVars = Set.filter isEffectVar $
                                       fv env `Set.union` fv ty
        observableRegions    = fr env `Set.union` fr ty

-------------------------------------------------
-- * Effect Constraints

data Constraint = !TyVar :>= !Effect

type Constraints = [Constraint]

instance Show Constraint where
  show (f :>= s) = show f ++ " >= " ++ show s

instance FV Constraint where
  fv (f :>= s) = Set.insert f $ fv s

instance FR Constraint where
  fr (_ :>= s) = fr s

instance SubstTarget Constraint where
  u $. (f :>= s) = f :>= (u $. s)

k2subst :: Constraints -> Subst
k2subst = foldr (++.) Subst.id . map mk
  where mk (f :>= s) = Subst.var2effect f (VarEff f :+ s)

infixr 9 $$.
($$.) :: SubstTarget a => Constraints -> a -> a
k $$. x = k2subst k $. x

-- * Signatures

data CSig = CForallTy !TyVars !Type !Constraints

instance Show CSig where
  show (CForallTy vs t k) = "forall " ++ vs_str ++ ". " ++
                                    show t ++ " & " ++ show k
    where vs_str = unwords (map show vs)

instance FV CSig where
  fv (CForallTy vs t cs) = (fv t `Set.union` fv cs) Set.\\ Set.fromList vs

instance FR CSig where
  fr (CForallTy vs t cs) = (fr t `Set.union` fr cs) Set.\\ vrs
    where vrs = Set.fromList $ map VarReg $ filter isRegionVar vs

instance SubstTarget CSig where
  u $. (CForallTy vs t cs) = CForallTy vs (u' $. t) (u' $. cs)
    where u' = u Subst.\\ vs

-- ** Free Variables

cfv :: (FV a,SubstTarget a) => Constraints -> a -> Set TyVar
cfv k = fv . (k$$.)

-- ** Free Regions

cfr :: (FR a,SubstTarget a) => Constraints -> a -> Set Region
cfr k = fr . (k$$.)

-- ** Type Generalization

cgen :: Constraints -> Effect -> Env -> Type -> CSig
cgen k ef env ty = CForallTy vars ty k
  where vars = toList $ cfv k ty Set.\\ (cfv k env `Set.union` cfv k ef)

-- ** Observable Effects

cobserve :: Constraints -> Env -> Type -> Effect -> Effect
cobserve k env ty ef = observe (k $$. env) (k $$. ty) (k $$. ef)
