
-- | One-shot subsitution for type variables
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

id :: Subst
id = Subst Map.empty Map.empty Map.empty

var2region :: TyVar -> Region -> Subst
var2region y p = Subst (Map.singleton y p) Map.empty Map.empty

var2effect :: TyVar -> Effect -> Subst
var2effect f s = Subst Map.empty (Map.singleton f s) Map.empty

var2type :: TyVar -> Type -> Subst
var2type a t = fromList [(a,t)]

fromList :: [(TyVar,Type)] -> Subst
fromList = Subst Map.empty Map.empty . Map.fromList

infixl 7 ++.
(++.) :: Subst -> Subst -> Subst
(Subst r1 e1 t1) ++. (Subst r2 e2 t2) =
  Subst (Map.union r1 r2) (Map.union e1 e2) (Map.union t1 t2)

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

instance SubstTarget Region where
  _ $. p@(Reg _) = p
  u $. p@(VarReg y)
    | Just p' <- Map.lookup y (regMap u)
    = p'
    | otherwise
    = p

instance SubstTarget Effect where
  _ $. s@EmptyEff = s
  u $. s@(VarEff f)
    | Just s' <- Map.lookup f (effMap u)
    = s'
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
    = t'
    | otherwise
    = t
  u $. (RefTy p t) = RefTy (u $. p) (u $. t)
  u $. (FunTy t1 s t2) = FunTy (u $. t1) (u $. s) (u $. t2)
