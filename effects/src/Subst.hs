
-- | Substitution for type-level variables
module Subst where

import           Data.Map.Strict ( Map )
import qualified Data.Map as Map

import Syntax

-------------------------------------------------
-- * Substitutions

data Subst = Subst {
    regMap :: Map TyVar Region
  , effMap :: Map TyVar Effect
  , typMap :: Map TyVar Type
  }
  deriving Show

id :: Subst
id = Subst Map.empty Map.empty Map.empty

fromList :: [(TyVar,TyVar)] -> Subst
fromList ps = Subst rr ee tt
  where rr = Map.fromList [ (v,VarReg w) | (v,w) <- ps, isRegionVar v ]
        ee = Map.fromList [ (v,VarEff w) | (v,w) <- ps, isEffectVar v ]
        tt = Map.fromList [ (v,VarTy w)  | (v,w) <- ps, isTypeVar v ]

var2region :: TyVar -> Region -> Subst
var2region y p@(VarReg _)
  | VarReg y /= p = Subst (Map.singleton y p) Map.empty Map.empty
  | otherwise     = Subst.id
var2region _ _ = error "var2region: mapping to a non-variable"

var2effect :: TyVar -> Effect -> Subst
var2effect f s
  | VarEff f /= s = Subst Map.empty (Map.singleton f s) Map.empty
  | otherwise     = Subst.id

var2type :: TyVar -> Type -> Subst
var2type a t
  | VarTy a /= t = Subst Map.empty Map.empty (Map.singleton a t)
  | otherwise    = Subst.id

-- cleanup :: Subst -> Subst
-- cleanup (Subst rr ee tt) = Subst rr' ee' tt'
--   where rr' = Map.filterWithKey (\k x -> x /= VarReg k) rr
--         ee' = Map.filterWithKey (\k x -> x /= VarEff k) ee
--         tt' = Map.filterWithKey (\k x -> x /= VarTy k) tt

infixl 7 ++.
(++.) :: Subst -> Subst -> Subst
u1@(Subst r1 e1 t1) ++. u2 =
  Subst (Map.union r1 r2) (Map.union e1 e2) (Map.union t1 t2)
  where (Subst r2 e2 t2) = u1 $. u2

(\\) :: Subst -> [TyVar] -> Subst
(Subst rr ee tt) \\ vs = Subst (deleteVars rr) (deleteVars ee) (deleteVars tt)
  where deleteVars = Map.filterWithKey (\k _ -> k `notElem` vs)

-------------------------------------------------
-- * Perform Substitution

infixr 9 $.
class SubstTarget a where
  ($.) :: Subst -> a -> a

instance SubstTarget a => SubstTarget [a] where
  u $. xs = map (u $.) xs

instance SubstTarget Subst where
  u $. (Subst rr ee tt) = Subst rr' ee' tt'
    where rr' = Map.map (u $.) rr
          ee' = Map.map (u $.) ee
          tt' = Map.map (u $.) tt

instance SubstTarget Region where
  _ $. p@(Reg _) = p
  u $. p@(VarReg y)
    | Just p' <- Map.lookup y (regMap u)
    = u $. p'
    | otherwise
    = p

instance SubstTarget Effect where
  _ $. s@EmptyEff = s
  u $. s@(VarEff f)
    | Just s' <- Map.lookup f (effMap u)
    -- k2subst introduces circular subsitutions and thus we need to be
    -- sure we break this circularity by removing the already substituted
    -- variable from the domain of the substitution.
    = (u \\ [f]) $. s'
    | otherwise
    = s
  u $. (InitEff p t) = InitEff (u $. p) (u $. t)
  u $. (ReadEff p) = ReadEff (u $. p)
  u $. (WriteEff p) = WriteEff (u $. p)
  u $. (s1 :+ s2) = (u $. s1) :+ (u $. s2)

instance SubstTarget Type where
  _ $. UnitTy = UnitTy
  u $. t@(VarTy a)
    | Just t' <- Map.lookup a (typMap u)
    = u $. t'
    | otherwise
    = t
  u $. (RefTy p t) = RefTy (u $. p) (u $. t)
  u $. (FunTy t1 s t2) = FunTy (u $. t1) (u $. s) (u $. t2)
