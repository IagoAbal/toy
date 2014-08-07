
module Unify where

import qualified Data.Set as Set

import           Syntax
import           Subst ( Subst, (++.), ($.) )
import qualified Subst

infix 8 `unify`
unify :: Type -> Type -> Subst
unify UnitTy      UnitTy      = Subst.id
unify (VarTy a)   b@(VarTy _) = Subst.var2type a b
unify (VarTy a)   ty          = unifyVar a ty
unify ty          (VarTy b)   = unifyVar b ty
unify (RefTy (VarReg y) a)
      (RefTy r@(VarReg _) b)
  = theta$.a `unify` theta$.b ++. theta
  where theta = Subst.var2region y r
unify (FunTy a1    (VarEff x1) b1)
      (FunTy a2 x2@(VarEff _)  b2)
  = theta$.b1`unify` theta$.b2 ++. theta
  where theta1 = Subst.var2effect x1 x2
        theta2 = theta1$.a1 `unify` theta1$.a2
        theta  = theta1 ++. theta2
unify _ _ = error "cannot unify"

unifyVar :: TyVar -> Type -> Subst
unifyVar a ty
  | a `Set.member` fv ty = error "unifyVar: occurs check"
  | otherwise            = Subst.var2type a ty