
module Infer where

import Subst ( Subst )
import Syntax

data Constraint = !Var :>= !Effect

type Constraints = [Constraint]

infer' :: Env -> Exp -> (Subst,Type,Effect,Constraints)
infer' = undefined