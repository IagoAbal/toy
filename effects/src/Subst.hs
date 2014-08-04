
module Subst where

import Syntax

data Subst = Subst

id :: Subst
id = undefined

infixl 7 ++.
(++.) :: Subst -> Subst -> Subst
s1 ++. s2 = undefined

infixr 9 $.
($.) :: Subst -> Type -> Type
s $. a = undefined

var2region :: Var -> Region -> Subst
var2region = undefined

var2effect :: Var -> Effect -> Subst
var2effect = undefined

var2type :: Var -> Type -> Subst
var2type a ty = undefined

substType :: Subst -> Type -> Type
substType = undefined
