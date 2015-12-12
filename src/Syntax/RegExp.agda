open import Data.List as List
open import Data.List.Properties
open List-solver renaming (nil to :[] ; _⊕_ to _:++_; _⊜_ to _:==_)
open import Data.Product renaming (_×_ to _*_)

open import Relation.Binary
open import Relation.Binary.PropositionalEquality renaming (_≡_ to _==_)
open import Relation.Nullary renaming (¬_ to not)

module Syntax.RegExp {Token : Set}(eqTokenDec : Decidable {A = Token} _==_)  where

  -- definition of regular expression syntax.

  infixr 5 _+_
  infixr 6 _o_
  infixl 7 _*

  data RegExp : Set where
    Emp : RegExp
    Eps : RegExp
    #_  : (a : Token) -> RegExp
    _o_ : (e e' : RegExp) -> RegExp
    _+_ : (e e' : RegExp) -> RegExp
    _*  : (e : RegExp) -> RegExp

  
