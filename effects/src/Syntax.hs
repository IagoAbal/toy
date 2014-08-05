module Syntax where

import           Data.Set ( Set )
import qualified Data.Set as Set

import Unique ( Uniq )

-------------------------------------------------
-- * Types

data Type = UnitTy
           | VarTy !TyVar
           | RefTy !Region !Type
           | FunTy !Type !Effect !Type
  deriving (Eq,Ord)

data Sig = ForallTy !TyVars !Type

-- ** Variables

type TyVars = [TyVar]

data TyVar =
  TyVar {
     tvKind :: !Kind
  ,  tvUniq :: !Uniq
  }
  deriving (Eq,Ord)

data Kind = RegKind
          | EffKind
          | TypKind
  deriving (Eq,Ord)

isEffectVar :: TyVar -> Bool
isEffectVar (TyVar EffKind _) = True
isEffectVar __other__         = False

-- ** Regions

data RegionId = RID !Int
  deriving (Eq,Ord)

data Region = Reg !RegionId
                -- ^ Region constants
             | VarReg !TyVar
                -- ^ Region variables
  deriving (Eq,Ord)

-- ** Effects

data Effect = EmptyEff
                -- ^ No effect
             | VarEff !TyVar
                -- ^ Effect variable
             | InitEff !Region !Type
                -- ^ Alloc effect
             | ReadEff !Region
                -- ^ Read effect
             | WriteEff !Region
                -- ^ Write effect
             | !Effect :+ !Effect
                -- ^ Effect union
  deriving (Eq,Ord)

type StoreEffect = Effect

effectTyVars :: Effect -> Set TyVar
effectTyVars = undefined

storeEffects :: Effect -> Set StoreEffect
storeEffects = undefined

storeRegion :: StoreEffect -> Region
storeRegion (InitEff r _) = r
storeRegion (ReadEff r)   = r
storeRegion (WriteEff r)  = r
storeRegion __other__     = error "storeRegion: not a store effect"

-------------------------------------------------
-- * Expressions

type Var = String

data Exp = Var !Var
         | Lam !Var !Exp
         | Let !Var !Exp !Exp
         | App !Exp !Exp

-------------------------------------------------
-- * Free TyVariables

class FV a where
  fv :: a -> Set TyVar

instance FV Region where
  fv (Reg _)    = Set.empty
  fv (VarReg y) = Set.singleton y

instance FV Effect where
  fv EmptyEff      = Set.empty
  fv (VarEff f)    = Set.singleton f
  fv (InitEff p t) = fv p `Set.union` fv t
  fv (ReadEff p)   = fv p
  fv (WriteEff p)  = fv p
  fv (s1 :+ s2)    = fv s1 `Set.union` fv s2

instance FV Type where
  fv UnitTy          = Set.empty
  fv (VarTy a)       =  Set.singleton a
  fv (RefTy p t)     = fv p `Set.union` fv t
  fv (FunTy t1 s t2) = Set.unions [fv t1,fv s,fv t2]

instance FV Sig where
  fv (ForallTy vs t) = fv t Set.\\ Set.fromList vs

-------------------------------------------------
-- * Region Constants

class FR a where
  fr :: a -> Set Region

instance FR Effect where
  fr EmptyEff      = Set.empty
  fr (VarEff _)    = Set.empty
  fr (InitEff p t) = Set.singleton p `Set.union` fr t
  fr (ReadEff p)   = Set.singleton p
  fr (WriteEff p)  = Set.singleton p
  fr (s1 :+ s2)    = fr s1 `Set.union` fr s2

instance FR Type where
  fr UnitTy          = Set.empty
  fr (VarTy _)       = Set.empty
  fr (RefTy p t)     = Set.singleton p `Set.union` fr t
  fr (FunTy t1 s t2) = Set.unions [fr t1,fr s,fr t2]
