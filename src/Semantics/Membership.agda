open import Data.List as List
open import Data.List.Properties
open List-solver renaming (nil to :[] ; _⊕_ to _:++_; _⊜_ to _:==_)
open import Data.Product renaming (_×_ to _*_)

open import Relation.Binary
open import Relation.Binary.PropositionalEquality renaming (_≡_ to _==_)
open import Relation.Nullary renaming (¬_ to not)

module Semantics.Membership {Token : Set}(eqTokenDec : Decidable {A = Token} _==_) where

  open import Syntax.RegExp eqTokenDec

  -- regular expression membership

  infix 3 _<-[[_]]
  infixr 6 _*_<=_
  infixr 6 _<+_ _+>_

  data _<-[[_]] : List Token -> RegExp -> Set where
    Eps    : List.[] <-[[ Eps ]]
    #_     : (a : Token) -> List.[ a ] <-[[ # a ]]
    _*_<=_ : {xs ys zs : List Token}{e e' : RegExp}
             (pr : xs <-[[ e ]])(pr' : ys <-[[ e' ]])
             (eq : zs == xs ++ ys) -> zs <-[[ e o e' ]]
    _<+_   : {xs : List Token}{e : RegExp}(e' : RegExp)
             -> (pr : xs <-[[ e ]]) -> xs <-[[ e + e' ]]           
    _+>_   : {xs : List Token}{e' : RegExp}(e : RegExp)
             -> (pr : xs <-[[ e' ]]) -> xs <-[[ e + e' ]]
    _*     : {xs : List Token}{e : RegExp} ->
             xs <-[[ Eps + e o e * ]]      ->
             xs <-[[ e * ]]

  -- simple inversion lemma

  Emp<-Inv : {xs : List Token} -> not (xs <-[[ Emp ]])
  Emp<-Inv ()

