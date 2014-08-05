module Syntax where

-- import           Data.Map ( Map )
-- import qualified Data.Map as Map
import           Data.Set ( Set )
-- import qualified Data.Set as Set

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
  , _tvUniq :: !Uniq
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
             | UnionEff !Effect !Effect
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

fvRegion :: Region -> Set TyVar
fvRegion = undefined

fvEffect :: Effect -> Set TyVar
fvEffect = undefined

fvType :: Type -> Set TyVar
fvType = undefined

fvSig :: Sig -> Set TyVar
fvSig = undefined

-------------------------------------------------
-- * Region Constants

frEffect :: Effect -> Set Region
frEffect = undefined

frType :: Type -> Set Region
frType = undefined
