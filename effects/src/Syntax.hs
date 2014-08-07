{-# LANGUAGE OverloadedStrings #-}

module Syntax where

import           Data.Set ( Set )
import qualified Data.Set as Set
import           Data.String ( IsString(..) )

import Unique ( Uniq )

-------------------------------------------------
-- * Types

data Type =  UnitTy
           | VarTy !TyVar
           | RefTy !Region !Type
           | FunTy !Type !Effect !Type
  deriving (Eq,Ord)

instance Show Type where
  show UnitTy          = "unit"
  show (VarTy v)       = show v
  show (RefTy p t)     = "ref(" ++ show p ++ ',' : show t ++  ")"
  show (FunTy t1 s t2) = show t1 ++ " -{" ++ show s ++ "}-> " ++ show t2

data Sig = ForallTy !TyVars !Type

instance Show Sig where
  show (ForallTy vs t) = "forall " ++ vs_str ++ ". " ++ show t
    where vs_str = unwords (map show vs)

-- ** Variables

type TyVars = [TyVar]

data TyVar =
  TyVar {
     tvKind :: !Kind
  ,  tvUniq :: !Uniq
  }
  deriving (Eq,Ord)

instance Show TyVar where
  show (TyVar RegKind i) = "%r" ++ show i
  show (TyVar EffKind i) = "!e" ++ show i
  show (TyVar TypKind i) = "'t" ++ show i

data Kind = RegKind
          | EffKind
          | TypKind
  deriving (Eq,Ord)

isEffectVar :: TyVar -> Bool
isEffectVar = (== EffKind) . tvKind

isRegionVar :: TyVar -> Bool
isRegionVar = (== RegKind) . tvKind

isTypeVar :: TyVar -> Bool
isTypeVar = (== TypKind) . tvKind

-- ** Regions

data RegionId = RID !Int
  deriving (Eq,Ord)

instance Show RegionId where
  show (RID i) = show i

data Region = Reg !RegionId
                -- ^ Region constants
             | VarReg !TyVar
                -- ^ Region variables
  deriving (Eq,Ord)

instance Show Region where
  show (Reg rid)  = "%R" ++ show rid
  show (VarReg y) = show y

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

instance Show Effect where
  show EmptyEff      = "0"
  show (VarEff f)    = show f
  show (InitEff p s) = "I(" ++ show p ++ ',' : show s ++ ")"
  show (ReadEff p)   = "R(" ++ show p ++ ")"
  show (WriteEff p)  = "W(" ++ show p ++ ")"
  show (s1 :+ s2)    = show s1 ++ " U " ++ show s2

(+:) :: Effect -> Effect -> Effect
EmptyEff +: s2       = s2
s1       +: EmptyEff = s1
s1       +: s2       = s1 :+ s2

sumEff :: [Effect] -> Effect
sumEff = foldr (+:) EmptyEff

type StoreEffect = Effect

effectVars :: Effect -> Set TyVar
effectVars =  Set.filter isEffectVar . fv

storeEffects :: Effect -> Set StoreEffect
storeEffects   EmptyEff      = Set.empty
storeEffects   (VarEff _)    = Set.empty
storeEffects s@(InitEff _ _) = Set.singleton s
storeEffects s@(ReadEff _)   = Set.singleton s
storeEffects s@(WriteEff _)  = Set.singleton s
storeEffects   (s1 :+ s2)    = storeEffects s1 `Set.union` storeEffects s2

storeRegion :: StoreEffect -> Region
storeRegion (InitEff r _) = r
storeRegion (ReadEff r)   = r
storeRegion (WriteEff r)  = r
storeRegion __other__     = error "storeRegion: not a store effect"

-------------------------------------------------
-- * Expressions

type Var = String

data Exp = Unit
         | Var !Var
         | Lam !Var !Exp
         | Let !Var !Exp !Exp
         | App !Exp !Exp
         | If !Exp !Exp
         | !Exp :- !Exp
  deriving Show

instance IsString Exp where
  fromString = Var

-------------------------------------------------
-- * Free TyVariables

class FV a where
  fv :: a -> Set TyVar

instance FV a => FV [a] where
  fv = Set.unions . map fv

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

instance FR a => FR [a] where
  fr = Set.unions . map fr

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
