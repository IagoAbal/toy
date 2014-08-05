{-# LANGUAGE ParallelListComp #-}

module Infer where

import           Control.Applicative ( (<$>) )

import           Data.Foldable ( toList )
import           Data.Map.Strict ( Map )
-- import qualified Data.Map as Map
import           Data.Set ( Set )
import qualified Data.Set as Set

import           Subst ( Subst, ($.), (++.) )
import qualified Subst
import           Syntax
import           Unify ( unify )
import           Unique ( Unique )
import qualified Unique as Uniq

infer :: Env -> Exp -> TI ({-Subst,-}Type,Effect,Constraints)
infer env e = do
  (theta,ty,ef,k) <- infer' env e
  return ({-theta,-}ty,observe k (theta$<env) ty ef,k)

infer' :: Env -> Exp -> TI (Subst,Type,Effect,Constraints)
infer' env (Var x)
  | Just (ForallTy as ty,k) <- lookupVar env x
  = do bs <- freshVars as
       let theta = Subst.fromList [ (a,VarTy b) | a <- as | b <- bs ]
       return (Subst.id,theta$.ty,EmptyEff,theta$$k)
  | otherwise
  = error "infer': variable not found"
infer' env (Lam x e) = do
  a <- freshVarTy
  l <- freshVar EffKind
  (theta,ty,eff,k) <- infer' (extendEnv env x (ForallTy [] a)) e
  return (theta,FunTy (theta$.a) (VarEff l) ty,EmptyEff,l :>= eff : k)
infer' env (Let x e e') = do
  (theta,ty,ef,k) <- infer' env e
  let env1 = theta$<env
      env' = extendEnv env1 x (gen k ef env1 ty)
  (theta',ty',ef',k') <- infer' env' e'
  return (theta'++.theta,ty',(theta'$.ef) :+ ef',(theta'$$k) ++ k')
infer' env (App e e') = do
  (theta,ty,ef,k) <- infer' env e
  (theta',ty',ef',k') <- infer' (theta$<env) e'
  a <- freshVarTy
  ee <- freshVarEff
  let theta'' = (theta'$.ty) `unify` FunTy ty' ee a
      theta1  = theta''++.theta'++.theta
      ty1     = theta''$.a
      ef1     = theta''$.((theta'$.ef) :+ ef' :+ ee)
      k1      = theta''$$(theta'$$k ++ k')
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

data Env = Env !(Map Var (Sig,Constraints))

lookupVar :: Env -> Var -> Maybe (Sig,Constraints)
lookupVar = undefined

extendEnv :: Env -> Var -> Sig -> Env
extendEnv = undefined

fvEnv :: Env -> Set TyVar
fvEnv = undefined

frEnv :: Env -> Set Region
frEnv = undefined

($<) :: Subst -> Env -> Env
_ $< _ = undefined

-------------------------------------------------
-- * Effect Constraints

data Constraint = !TyVar :>= !Effect

type Constraints = [Constraint]

($$) :: Subst -> Constraints -> Constraints
_ $$ _ = undefined

-------------------------------------------------
-- * Type Generalization

gen :: Constraints -> Effect -> Env -> Type -> Sig
gen = undefined
-- gen oEff env ty = ForallTy vars ty
--   where vars = toList $ fvType ty Set.\\ (fvEnv env `Set.union` fvEffect oEff)

-------------------------------------------------
-- * Observable Effects

observe :: Constraints -> Env -> Type -> Effect -> Effect
observe = undefined
-- observe env ty eff = Set.fromList $
--      [ VarEff x | x <- toList $ effectTyVars eff
--                 , x `Set.member` observableEffectTyVars
--                 ]
--   ++ [ se | se <- toList $ storeEffects eff
--           , storeRegion se `Set.member` observableRegions
--           ]
--   where observableEffectTyVars = Set.filter isEffectVar $
--                                        fvEnv env `Set.union` fvType ty
--         observableRegions    = frEnv env `Set.union` frType ty