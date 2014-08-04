module Syntax where

import           Data.Foldable ( toList )
import           Data.Map ( Map )
-- import qualified Data.Map as Map
import           Data.Set ( Set )
import qualified Data.Set as Set

-- * Abstract Syntax

type Vars = [Var]

data Var = Var VarKind !Int
  deriving (Eq,Ord)

data VarKind = RegKind
              | EffKind
              | TypKind
  deriving (Eq,Ord)

isEffectVar :: Var -> Bool
isEffectVar (Var EffKind _) = True
isEffectVar __other__       = False

data RegionId = RID !Int
  deriving (Eq,Ord)

data Region = Reg !RegionId
                -- ^ Region constants
             | VarReg !Var
                -- ^ Region variables
  deriving (Eq,Ord)


data Effect = EmptyEff
                -- ^ No effect
             | VarEff !Var
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

data Type = UnitTy
           | VarTy !Var
           | RefTy !Region !Type
           | FunTy !Type !Effect !Type
  deriving (Eq,Ord)

data Sig = ForallTy !Vars !Type

data Exp = Exp

-- * Effects

type StoreEffect = Effect

effectVars :: Effect -> Set Var
effectVars = undefined

storeEffects :: Effect -> Set StoreEffect
storeEffects = undefined

storeRegion :: StoreEffect -> Region
storeRegion (InitEff r _) = r
storeRegion (ReadEff r)   = r
storeRegion (WriteEff r)  = r
storeRegion __other__      = error "storeRegion: not a store effect"

-- * Typing Environment

data Env = Env (Map Var Sig)

-- * Free Variables

fvRegion :: Region -> Set Var
fvRegion = undefined

fvEffect :: Effect -> Set Var
fvEffect = undefined

fvType :: Type -> Set Var
fvType = undefined

fvSig :: Sig -> Set Var
fvSig = undefined

fvEnv :: Env -> Set Var
fvEnv = undefined

-- * Region Constants

frEffect :: Effect -> Set Region
frEffect = undefined

frType :: Type -> Set Region
frType = undefined

frEnv :: Env -> Set Region
frEnv = undefined

-- * Type Generalization

gen :: Effect -> Env -> Type -> Sig
gen oEff env ty = ForallTy vars ty
  where vars = toList $ fvType ty Set.\\ (fvEnv env `Set.union` fvEffect oEff)

-- * Observable Effects

observe :: Env -> Type -> Effect -> Set Effect
observe env ty eff = Set.fromList $
     [ VarEff x | x <- toList $ effectVars eff
                , x `Set.member` observableEffectVars
                ]
  ++ [ se | se <- toList $ storeEffects eff
          , storeRegion se `Set.member` observableRegions
          ]
  where observableEffectVars = Set.filter isEffectVar $
                                       fvEnv env `Set.union` fvType ty
        observableRegions    = frEnv env `Set.union` frType ty
