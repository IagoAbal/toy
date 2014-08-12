
module Constraint where

import           Data.Foldable ( toList )
import           Data.Function ( on )
import qualified Data.List as List
import           Data.Set ( Set )
import qualified Data.Set as Set

import           Subst ( Subst, SubstTarget(..), (++.) )
import qualified Subst
import           Syntax

import Debug.Trace ( trace )

-------------------------------------------------
-- * Effect Constraints

data Constraint = !TyVar :>= !Effect
  deriving Eq

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
                    __other__ -> f

k2subst :: Constraints -> Subst
k2subst = foldr (++.) Subst.id . map mk
  where mk (f :>= s) = Subst.var2effect f (VarEff f +: s)

infixr 9 $$.
($$.) :: SubstTarget a => Constraints -> a -> a
k $$. x = k2subst k $. x

(\\) :: Constraints -> Set TyVar -> Constraints
k \\ xs = filter (\(y :>= _) -> y `Set.notMember` xs) k


-------------------------------------------------
-- * Well-Formed Constraint Sets

wf :: Constraints -> Bool
wf k = and [ wf_c c k' | c <- k, let k' = List.delete c k ]

wf_c :: Constraint -> Constraints -> Bool
wf_c (f :>= s) k' = and
  [  f `Set.notMember` fv t
  | InitEff _ t <- toList $ storeEffects $ k' $$. s
  ]

-------------------------------------------------
-- * Solving

findVar :: TyVar -> Constraints -> [Effect]
findVar _y []          = []
findVar  y (x :>= s:k)
        | y == x       = s : findVar y k
        | otherwise    = findVar y k

solution0 :: Set TyVar -> Subst
solution0 = Set.foldl'
                (\u x -> u ++. Subst.var2effect x EmptyEff)
                Subst.id

lfp :: Int -> (a -> a -> Bool) -> (a -> a) -> a -> a
lfp 0    _ _ x = x
lfp k stop f x
  | stop x y  = y
  | otherwise = lfp (k-1) stop f y
  where y = f x

updateVar :: TyVar -> Effect -> Subst -> Subst
updateVar x s1 u = Subst.var2effect x (s0 +: s1)
  where s0 = u $. VarEff x

solve :: Set TyVar -> Constraints -> (Subst,Constraints)
solve vars k = let (u',k') = lfp 42 {- :-) -} ((==) `on` fst) go (u0,k0)
                 in (u',k' Constraint.\\ vars)
  where u0 = solution0 vars
        k0 = u0 $. k
        go :: (Subst,Constraints) -> (Subst,Constraints)
        go (u1,k1) = (u2,k2)
          where u2 = step u1 k1
                k2 = u2 $. k1
        step :: Subst -> Constraints -> Subst
        step u []               = u
        step u (x :>= s:k')
          | x `Set.member` vars = updateVar x s u ++. u'
          | otherwise           = u'
          where u' = step u k'