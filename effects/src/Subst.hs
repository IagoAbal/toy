
module Subst where

import Syntax

data Subst = Subst

id :: Subst
id = undefined

infixl 7 ++.
(++.) :: Subst -> Subst -> Subst
_ ++. _ = undefined

infixr 9 $.
($.) :: Subst -> Type -> Type
_ $. _ = undefined

infixr 9 $:
($:) :: Subst -> Effect -> Effect
_ $: _ = undefined

var2region :: TyVar -> Region -> Subst
var2region = undefined

var2effect :: TyVar -> Effect -> Subst
var2effect = undefined

var2type :: TyVar -> Type -> Subst
var2type = undefined

fromList :: [(TyVar,Type)] -> Subst
fromList = undefined

substType :: Subst -> Type -> Type
substType = undefined
