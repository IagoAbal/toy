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

import Debug.Trace

-------------------------------------------------
-- * Type Inferece

ti :: Exp -> (Type,Effect,Constraints)
ti e = (ty,ef,k) -- cgen k ef tiEnv ty
  where (ty,ef,k) = Uniq.evalUnique (infer tiEnv e) tiSupply
        tiSupply = Uniq.mkSupply 10
        tiEnv = Env $ Map.fromList
                  [ ("new",new_sig)
                  , ("get",get_sig)
                  , ("set",set_sig)
                  ]
          where new_sig = CForallTy [a,y,f]
                                    (FunTy t s (RefTy p t))
                                    [f :>= InitEff p t]
                  where a = TyVar TypKind 0
                        t = VarTy a
                        y = TyVar RegKind 1
                        p = VarReg y
                        f = TyVar EffKind 2
                        s = VarEff f
                get_sig = CForallTy [a,y,f]
                                    (FunTy (RefTy p t) s t)
                                    [f :>= ReadEff p]
                  where a = TyVar TypKind 3
                        t = VarTy a
                        y = TyVar RegKind 4
                        p = VarReg y
                        f = TyVar EffKind 5
                        s = VarEff f
                set_sig = CForallTy [a,y,f,f']
                                    (FunTy (RefTy p t) s
                                        (FunTy t s' UnitTy))
                                    [f' :>= WriteEff p]
                  where a = TyVar TypKind 6
                        t = VarTy a
                        y = TyVar RegKind 7
                        p = VarReg y
                        f = TyVar EffKind 8
                        s = VarEff f
                        f' = TyVar EffKind 9
                        s' = VarEff f'

infer :: Env -> Exp -> TI (Type,Effect,Constraints)
infer env e = do
  (u,ty,ef,k) <- infer' env e
  let env' = u $. env
      oEf = cobserve k env' ty ef
  trace ("\n-----------" ++
         "\nINFER " ++ show e ++
         "\n  ty  = " ++ show ty ++
         "\n  ef  = " ++ show ef ++
         "\n  k = " ++ show k ++
         "\n  oEf = " ++ show oEf
     ) $ return ()
  return (ty,oEf,k)

infer' :: Env -> Exp -> TI (Subst,Type,Effect,Constraints)

infer' _env Unit = return (Subst.id,UnitTy,EmptyEff,[])

infer' env ee@(Var x)
  | Just (CForallTy as ty k) <- lookupVar env x
  = do bs <- freshVars as
       let u   = Subst.fromList $ zip as bs
           ty' = u $. ty
           k'  = u $. k
       trace ("\n-----------" ++
              "\nVAR " ++ show ee ++
              "\n  as  = " ++ show as ++
              "\n  bs  = " ++ show bs ++
              "\n  ty  = " ++ show ty ++
              "\n  ty' = " ++ show ty' ++
              "\n  k   = " ++ show k ++
              "\n  k'  = " ++ show k'
          ) $ return ()
       return (Subst.id,ty',EmptyEff,k')
  | otherwise
  = error "infer': variable not found"

infer' env ee@(Lam x e) = do
  a <- freshVarTy
  s@(VarEff f) <- freshVarEff
  (u,ty,ef,k) <- infer' (extendEnv x (CForallTy [] a []) env) e
  let a' = u $. a
  trace ("\n-----------" ++
         "\nLAM " ++ show ee ++
         "\n  a  = " ++ show a ++
         "\n  s  = " ++ show s ++
         "\n  ty  = " ++ show ty ++
         "\n  ef = " ++ show ef ++
         "\n  k   = " ++ show k
     ) $ return ()
  return (u,FunTy a' s ty,EmptyEff,f :>= ef : k)

infer' env (Let x e e') = do
  (theta,ty,ef,k) <- infer' env e
  let env1 = theta$.env
      env' = extendEnv x (cgen k ef env1 ty) env1
  (theta',ty',ef',k') <- infer' env' e'
  return (theta'++.theta,ty',(theta'$.ef) +: ef',(theta'$.k) ++ k')

infer' env ee@(App e e') = do
  (u,ty,s,k) <- infer' env e
  (u',ty',s',k') <- infer' (u $. env) e'
  a <- freshVarTy
  s1 <- freshVarEff
  let u'' = (u' $. ty) `unify` FunTy ty' s1 a
      u1  = u'' ++. u' ++. u
      ty1 = u'' $. a
      ef1 = u'' $. ((u' $. s) +: s' +: s1)
      k1  = u'' $. (u' $. k ++ k')
  trace ("\n-----------" ++
         "\nAPP " ++ show ee ++
         "\n  ty  = " ++ show ty ++
         "\n  s  = " ++ show s ++
         "\n  k  = " ++ show k ++
         "\n  ty'  = " ++ show ty' ++
         "\n  s' = " ++ show s' ++
         "\n  k'  = " ++ show k' ++
         "\n  a   = " ++ show a ++
         "\n  s1  = " ++ show s1 ++
         "\n  ty1  = " ++ show ty1 ++
         "\n  ef1   = " ++ show ef1 ++
         "\n  k1   = " ++ show k1
     ) $ return ()
  return (u1,ty1,ef1,k1)

infer' env (If e1 e2) = do
  (u1,ty1,s1,k1) <- infer' env e1
  (u2,ty2,s2,k2) <- infer' (u1 $. env) e2
  let ty1' = u2 $. ty1
      u0 = ty1' `unify` ty2
      ty = u0 $. ty1'
      ef = u0 $. ((u2 $. s1) +: s2)
      k = u0 $. (u2 $. k1 ++ k2)
      u = u0 ++. u1 ++. u2
  return (u,ty,ef,k)

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
  deriving Show

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
  trace ("\n-----------" ++
       "\nOBSERVE " ++
       "\n  env  = " ++ show env ++
       "\n  ty  = " ++ show ty ++
       "\n  eff  = " ++ show eff ++
       "\n  observableEffectVars = " ++ show observableEffectVars ++
       "\n  observableRegions   = " ++ show observableRegions
   ) $
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
  u $. (f :>= s) = f' :>= (u $. s)
    where f' = case u $. VarEff f of
                    VarEff x  -> x
                    __other__ -> undefined

k2subst :: Constraints -> Subst
k2subst = foldr (++.) Subst.id . map mk
  where mk (f :>= s) = Subst.var2effect f (VarEff f +: s)

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
