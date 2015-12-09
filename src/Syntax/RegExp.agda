open import Relation.Binary
open import Relation.Binary.PropositionalEquality

module Syntax.RegExp {Token : Set}(eqTokenDec : Decidable {A = Token} _≡_)  where
