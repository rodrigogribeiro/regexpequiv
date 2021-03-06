open import Algebra

open import Data.List as List renaming (_∷_ to _::_)
open import Data.List.Properties
open List-solver renaming (nil to :[] ; _⊕_ to _:++_; _⊜_ to _:==_)
open import Data.Product renaming (_×_ to _*_ ; proj₁ to fst ; proj₂ to snd)

open import Function renaming (_∘_ to _:o:_)

open import Relation.Binary
open import Relation.Binary.PropositionalEquality renaming (_≡_ to _==_)
open import Relation.Nullary renaming (¬_ to not)

module Semantics.Equivalence {Token : Set}(eqTokenDec : Decidable {A = Token} _==_) where

  open import Syntax.RegExp eqTokenDec 
  open import Semantics.Membership eqTokenDec 

  -- regular expression equivalence

  infix 4 _:=:_

  _:=:_ : forall (e e' : RegExp) -> Set
  e :=: e' = forall (xs : List Token) -> (((pr : xs <-[[ e ]]) -> (xs <-[[ e' ]])) *
                                          ((pr : xs <-[[ e' ]]) -> (xs <-[[ e ]])))

  -- :=: is an equivalence relation

  :=:-refl : forall {e : RegExp} -> e :=: e
  :=:-refl xs = id , id

  :=:-sym : forall {e e' : RegExp} -> e :=: e' -> e' :=: e
  :=:-sym pr xs = snd (pr xs) , fst (pr xs)

  :=:-trans : forall {e e' e'' : RegExp} -> e :=: e' -> e' :=: e'' -> e :=: e''
  :=:-trans pr pr' xs = fst (pr' xs) :o: fst (pr xs) , snd (pr xs) :o: snd (pr' xs)

  RegExpEquiv : IsEquivalence _:=:_
  RegExpEquiv = record { refl = :=:-refl
                       ; sym = :=:-sym
                       ; trans = :=:-trans }

  -- congruence lemmas

  :=:-concatCong : forall {e e' f f' : RegExp} -> e :=: e' -> f :=: f' -> (e o f) :=: (e' o f')
  :=:-concatCong pr pr' xs = part1 pr pr' , part2 pr pr'
                             where
                               part1 : forall {e e' f f' : RegExp}{xs} -> e :=: e' -> f :=: f' -> xs <-[[ e o f ]] -> xs <-[[ e' o f' ]]
                               part1 pe pf (_*_<=_ {xs = xs}{ys = ys} pr pr' eq) rewrite eq = fst (pe xs) pr * fst (pf ys) pr' <= refl 

                               part2 : forall {e e' f f' : RegExp}{xs} -> e :=: e' -> f :=: f' -> xs <-[[ e' o f' ]] -> xs <-[[ e o f ]]
                               part2 pe pf (_*_<=_ {xs = xs}{ys = ys} pr pr' eq) rewrite eq = snd (pe xs) pr * snd (pf ys) pr' <= refl


  :=:-choiceCong : forall {e e' f f' : RegExp} -> e :=: e' -> f :=: f' -> (e + f) :=: (e' + f')
  :=:-choiceCong pr pr' xs = part1 pr pr' , part2 pr pr'
                             where
                               part1 : forall {e e' f f' : RegExp}{xs} -> e :=: e' -> f :=: f' -> xs <-[[ e + f ]] -> xs <-[[ e' + f' ]]
                               part1 pe pf (_+>_ {xs = xs} _ pr) = _ +> (fst (pf xs)) pr
                               part1 pe pf (_<+_ {xs = xs} _ pr) = _ <+ (fst (pe xs)) pr

                               part2 : forall {e e' f f' : RegExp}{xs} -> e :=: e' -> f :=: f' -> xs <-[[ e' + f' ]] -> xs <-[[ e + f ]]
                               part2 pe pf (_+>_ {xs = xs} _ pr) = _ +> snd (pf xs) pr
                               part2 pe pf (_<+_ {xs = xs} _ pr) = _ <+ snd (pe xs) pr


  -- lemma choice left

  lemChoiceEmpL : (e : RegExp) -> (e + Emp) :=: e
  lemChoiceEmpL e xs = part1 {xs = xs} e , part2 {xs = xs} e
                       where
                         part1 : forall {xs} e -> xs <-[[ e + Emp ]] -> xs <-[[ e ]]
                         part1 e' (.Emp <+ pr) = pr
                         part1 e' (.e' +> ())

                         part2 : forall {xs} e -> xs <-[[ e ]] -> xs <-[[ e + Emp ]]
                         part2 .Eps Eps = Emp <+ Eps
                         part2 .(# a) (# a) = Emp <+ # a
                         part2 ._ (pr * pr' <= eq) = Emp <+ pr * pr' <= eq
                         part2 ._ (e' <+ pr) = Emp <+ e' <+ pr
                         part2 ._ (e' +> pr) = Emp <+ e' +> pr
                         part2 ._ (pr *) = Emp <+ pr *

  lemChoiceEmpR : (e : RegExp) -> (Emp + e) :=: e
  lemChoiceEmpR e xs = part1 e , part2 e
                       where
                         part1 : forall {xs} e -> xs <-[[ Emp + e ]] -> xs <-[[ e ]]
                         part1 e (_ +> pr) = pr
                         part1 e (_ <+ ())

                         part2 : forall {xs} e -> xs <-[[ e ]] -> xs <-[[ Emp + e ]]
                         part2 e pr = _ +> pr

  -- lemma choice idempotent

  lemChoiceIdem : (e : RegExp) -> (e + e) :=: e
  lemChoiceIdem e xs = part1 xs e , part2 xs e
                       where
                         part1 : forall xs e -> xs <-[[ e + e ]] -> xs <-[[ e ]]
                         part1 _ e' (.e' <+ pr) = pr
                         part1 _ e' (.e' +> pr) = pr

                         part2 : forall xs e -> xs <-[[ e ]] -> xs <-[[ e + e ]]
                         part2 .[] .Eps Eps = Eps <+ Eps
                         part2 .(a :: []) .(# a) (# a) = # a <+ # a
                         part2 xs' ._ (pr * pr₁ <= eq) = (_ o _) <+ pr * pr₁ <= eq
                         part2 xs' ._ (e' <+ pr) = (_ + e') <+ e' <+ pr
                         part2 xs' ._ (e₁ +> pr) = (e₁ + _) <+ e₁ +> pr
                         part2 xs' ._ (pr *) = _ * <+ pr *

  -- lemma choice commutative

  lemChoiceComm : (e e' : RegExp) -> (e + e') :=: (e' + e)
  lemChoiceComm e e' xs = part1 xs e e'  , part2 xs e e'
                          where
                            part1 : forall xs e e' -> xs <-[[ e + e' ]] -> xs <-[[ e' + e ]]
                            part1 xs' e e' (_ <+ pr) = _ +> pr
                            part1 xs' e e' (_ +> pr) = _ <+ pr

                            part2 : forall xs e e' -> xs <-[[ e' + e ]] -> xs <-[[ e + e' ]]
                            part2 xs' e' e'' (_ <+ pr) = e' +> pr
                            part2 xs' e' e'' (_ +> pr) = e'' <+ pr


  -- lemma choice is associative

  lemChoiceAssoc : (e e' e'' : RegExp) -> (e + (e' + e'')) :=: ((e + e') + e'')
  lemChoiceAssoc e e' e'' xs = part1 xs e e' e'' , part2 xs e e' e''
                               where
                                 part1 : forall xs e e' e'' -> xs <-[[ e + e' + e'' ]] -> xs <-[[ (e + e') + e'' ]]
                                 part1 xs' e e' e'' (_ <+ pr) = e'' <+ e' <+ pr
                                 part1 xs' e' _ _ (_ +> _ <+ pr) = _ <+ e' +> pr
                                 part1 xs' e' _ _ (_ +> _ +> pr) = (e' + _) +> pr

                                 part2 : forall xs e e' e'' -> xs <-[[ (e + e') + e'' ]] -> xs <-[[ e + e' + e'' ]]
                                 part2 xs e e' e'' (_ <+ _ <+ pr) = (e' + e'') <+ pr
                                 part2 xs e e' e'' (_ <+ _ +> pr) = e +> e'' <+ pr
                                 part2 xs e e' e'' (_ +> pr) = e +> e' +> pr

  -- lemma concatenation neutral

  lemConcatEpsL : (e : RegExp) -> (e o Eps) :=: e
  lemConcatEpsL e xs = part1 xs e , part2 xs e
                       where
                         lem : forall {A : Set}(xs : List A) -> xs ++ [] == xs
                         lem = solve 1 (\ xs -> xs :++ :[] :== xs) refl

                         part1 : forall xs e -> xs <-[[ e o Eps ]] -> xs <-[[ e ]]
                         part1 .(xs' ++ []) e (_*_<=_ {xs = xs'} pr Eps refl) rewrite lem xs' = pr

                         part2 : forall xs e -> xs <-[[ e ]] -> xs <-[[ e o Eps ]]
                         part2 xs e pr = pr * Eps <= sym (lem xs)

  lemConcatEpsR : (e : RegExp) -> (Eps o e) :=: e
  lemConcatEpsR e xs = part1 xs e , part2 xs e
                       where
                         part1 : forall xs e -> xs <-[[ Eps o e ]] -> xs <-[[ e ]]
                         part1 xs e (_*_<=_ Eps pr' eq) rewrite eq = pr'

                         part2 : forall xs e -> xs <-[[ e ]] -> xs <-[[ Eps o e ]]
                         part2 xs e pr = Eps * pr <= refl

  -- lemma concatenation empty

  lemConcatEmpL : (e : RegExp) -> (Emp o e) :=: Emp
  lemConcatEmpL e xs = part1 xs e , part2 xs e
                       where
                         part1 : forall xs e -> xs <-[[ Emp o e ]] -> xs <-[[ Emp ]]
                         part1 xs e (() * pr' <= eq)

                         part2 : forall xs e -> xs <-[[ Emp ]] -> xs <-[[ Emp o e ]]
                         part2 xs e ()

  lemConcatEmpR : (e : RegExp) -> (e o Emp) :=: Emp
  lemConcatEmpR e xs = part1 xs e , part2 xs e
                       where
                         part1 : forall xs e -> xs <-[[ e o Emp ]] -> xs <-[[ Emp ]]
                         part1 xs e (_ * () <= _)

                         part2 : forall xs e -> xs <-[[ Emp ]] -> xs <-[[ e o Emp ]]
                         part2 xs e ()

  -- lemma concatenation is associative

  lemConcatAssoc : (e e' e'' : RegExp) -> (e o e' o e'') :=: ((e o e') o e'')
  lemConcatAssoc e e' e'' xs = part1 xs e e' e'' , part2 xs e e' e''
                               where
                                 lem : {A : Set}(xs ys zs : List A) -> xs ++ ys ++ zs == (xs ++ ys) ++ zs
                                 lem = solve 3 (\ xs ys zs -> xs :++ ys :++ zs :== (xs :++ ys) :++ zs) refl
                                 
                                 part1 : forall xs e e' e'' -> xs <-[[ e o e' o e'' ]] -> xs <-[[ (e o e') o e'' ]]
                                 part1 ._ e e' e'' (_*_<=_ {xs = xs}
                                                           {ys = .(xs' ++ ys')}
                                                           pr
                                                           (_*_<=_ {xs = xs'}{ys = ys'}
                                                           p q refl) refl) = (pr * p <= refl) * q <= lem xs xs' ys'

                                 part2 : forall xs e e' e'' -> xs <-[[ (e o e') o e'' ]] -> xs <-[[ e o e' o e'' ]]
                                 part2 ._ e e' e'' (_*_<=_ {xs = .(xs ++ ys)}
                                                           {ys = zs}
                                                           (_*_<=_ {xs = xs}
                                                                   {ys = ys} pr pr' refl)
                                                           pr'' eq) rewrite eq = pr * (pr' * pr'' <= refl) <= sym (lem xs ys zs)

  -- lemma concatenation distributes over choice

  lemConcatDistChoiceL : (e e' e'' : RegExp) -> e o (e' + e'') :=: (e o e') + (e o e'')
  lemConcatDistChoiceL e e' e'' xs = part1 xs e e' e'' , part2 xs e e' e''
                                     where
                                       part1 : forall xs e e' e'' -> xs <-[[ e o (e' + e'') ]] -> xs <-[[ e o e' + e o e'' ]]
                                       part1 xs e e' e'' (pr * (_ +> pr') <= eq) rewrite eq = _ +> (pr * pr' <= refl)
                                       part1 xs e e' e'' (pr * (_ <+ pr') <= eq) rewrite eq = _ <+ (pr * pr' <= refl)

                                       part2 : forall xs e e' e'' -> xs <-[[ e o e' + e o e'' ]] -> xs <-[[ e o (e' + e'') ]]
                                       part2 xs e e' e'' ( _ +> (pr * pr' <= eq)) = pr * (_ +> pr') <= eq
                                       part2 xs e e' e'' ( _ <+ (pr * pr' <= eq)) = pr * (_ <+ pr') <= eq
                                       
  lemConcatDistChoiceR : (e e' e'' : RegExp) -> (e + e') o e'' :=: (e o e'') + (e' o e'')
  lemConcatDistChoiceR e e' e'' xs = part1 xs e e' e'' , part2 xs e e' e''
                                     where
                                       part1 : forall xs e e' e'' -> xs <-[[ (e + e') o e'' ]] -> xs <-[[ (e o e'') + (e' o e'') ]]
                                       part1 xs e e' e'' ((_ +> pr) * pr' <= eq) rewrite eq = _ +> (pr * pr' <= refl)
                                       part1 xs e e' e'' ((_ <+ pr) * pr' <= eq) rewrite eq = _ <+ (pr * pr' <= refl)

                                       part2 : forall xs e e' e'' -> xs <-[[ (e o e'') + (e' o e'') ]] -> xs <-[[ (e + e') o e'' ]]
                                       part2 xs e e' e'' (_ +> (pr * pr' <= eq)) rewrite eq = (_ +> pr) * pr' <= refl
                                       part2 xs e e' e'' (_ <+ (pr * pr' <= eq)) rewrite eq = (_ <+ pr) * pr' <= refl

  -- kleene star relation with choice and concat

  lemStarChoiceConcat : (e : RegExp) -> e * :=: (Eps + e o e *)
  lemStarChoiceConcat e xs = part1 xs e , part2 xs e
                             where
                               part1 : forall xs e -> xs <-[[ e * ]] -> xs <-[[ Eps + e o e * ]]
                               part1 xs e (pr *) = pr

                               part2 : forall xs e -> xs <-[[ Eps + e o e * ]] -> xs <-[[ e * ]]
                               part2 xs e pr = pr *

  lemStarEps : (e : RegExp) -> e * :=: (Eps + e) *
  lemStarEps e xs = part1 xs e , part2 xs e
                    where
                      part1 : forall xs e -> xs <-[[ e * ]] -> xs <-[[ (Eps + e) * ]]
                      part1 xs e (( _ +> (pr * pr' <= eq)) *) rewrite eq = (_ +> ((_ +> pr) * (part1 _ _ pr') <= refl)) *
                      part1 xs e (( _ <+ pr) *) = (_ <+ pr) *

                      part2 : forall xs e -> xs <-[[ (Eps + e) * ]] -> xs <-[[ e * ]]
                      part2 xs e ((_ +> ((_ +> pr) * pr' <= eq)) *) rewrite eq = (_ +> pr * (part2 _ _ pr') <= refl) *
                      part2 xs e ((_ +> ((_<+_ {xs = []} _ Eps) * pr' <= eq)) *) rewrite eq = part2 _ _ pr'
                      part2 xs e ((_ <+ pr) *) = (_ <+ pr) *


  lemmaKleeneIdem : (e : RegExp) -> e * :=: (e *) *
  lemmaKleeneIdem e xs = subsetLemma (e *) , subsetLemma' e
                         where
                           mem : forall {xs e} -> xs <-[[ e ]] -> List _
                           mem {xs = xs} _ = xs

                           assoc1 : forall {A : Set}(xs ys zs : List A) -> (xs ++ ys) ++ zs == xs ++ (ys ++ zs)
                           assoc1 = solve 3 (\ xs ys zs -> (xs :++ ys) :++ zs :== xs :++ (ys :++ zs)) refl

                           lem' : forall {xs ys zs} e -> zs == xs ++ ys -> xs <-[[ e ]]  -> ys <-[[ e * ]] -> zs <-[[ e * ]]
                           lem' e refl pr pr' = (_ +> pr * pr' <= refl) *

                           lem : forall {xs ys zs} e -> zs == xs ++ ys -> xs <-[[ e * ]] -> ys <-[[ e * ]] -> zs <-[[ e * ]]
                           lem e refl ((.(e o e *) <+ Eps) *)    q = q
                           lem e eq ((.Eps +> p * p₁ <= refl) *) q rewrite assoc1 (mem p) (mem p₁) (mem q)
                               = lem' e eq p (lem e refl p₁ q)

                           subsetLemma' : forall {xs} e -> xs <-[[ e * * ]] -> xs <-[[ e * ]]
                           subsetLemma' e ((.(e * o e * *) <+ pr) *)   = ((e o e *) <+ pr) *
                           subsetLemma' e ((.Eps +> pr * pr₁ <= eq) *) = lem e eq pr (subsetLemma' e pr₁)

                           subsetLemma : forall {xs} e -> xs <-[[ e ]] -> xs <-[[ e * ]]
                           subsetLemma {xs = xs} e pr = (_ +> pr * ((_ <+ Eps) *) <= solve 1 (\ xs -> xs :== xs :++ :[]) refl xs) *


  -- algebraic structure of regular expressions

  concatSemigroup : Semigroup _ _
  concatSemigroup = record {
                    Carrier = RegExp
                    ; _≈_ = _:=:_
                    ; _∙_ = _o_
                    ; isSemigroup = record { isEquivalence = RegExpEquiv
                                   ; assoc = \ e e' e'' xs -> :=:-sym (lemConcatAssoc e e' e'') xs
                                   ; ∙-cong = :=:-concatCong } }

  concatMonoid : Monoid _ _
  concatMonoid
    = record { Carrier = RegExp
             ; _≈_ = _:=:_
             ; _∙_ = _o_
             ; ε = Eps
             ; isMonoid
               = record {
                        isSemigroup = isSemigroup concatSemigroup
                        ; identity = lemConcatEpsR , lemConcatEpsL } }
      where
        open Semigroup 

  choiceSemigroup : Semigroup _ _
  choiceSemigroup = record { Carrier = RegExp
                           ; _≈_ = _:=:_
                           ; _∙_ = _+_
                           ; isSemigroup = record {
                                   isEquivalence = RegExpEquiv
                                   ; assoc = \ e e' e'' xs -> :=:-sym (lemChoiceAssoc e e' e'') xs
                                   ; ∙-cong = :=:-choiceCong } }


  choiceMonoid : Monoid _ _
  choiceMonoid
    = record { Carrier = RegExp
             ; _≈_ = _:=:_
             ; _∙_ = _+_
             ; ε = Emp
             ; isMonoid
               = record {
                        isSemigroup
                          = isSemigroup choiceSemigroup
                        ; identity = lemChoiceEmpR , lemChoiceEmpL } }
      where
        open Semigroup

  regExpSemiring : Semiring _ _
  regExpSemiring = record
                     { Carrier = RegExp
                     ; _≈_ = _:=:_
                     ; _+_ = _+_
                     ; _*_ = _o_
                     ; 0# = Emp
                     ; 1# = Eps
                     ; isSemiring
                       = record {
                          isSemiringWithoutAnnihilatingZero
                          = record {
                            +-isCommutativeMonoid = record {
                                                    isSemigroup = isSemigroup choiceSemigroup
                                                    ; identityˡ = lemChoiceEmpR
                                                    ; comm = lemChoiceComm }
                            ; *-isMonoid = Monoid.isMonoid concatMonoid
                            ; distrib = leftdistr , (λ x y z xs → rightdistr y z x xs) }
                          ; zero = lemConcatEmpL , lemConcatEmpR }
                     }
                   where
                     leftdistr : forall (e e' e'' : RegExp) -> e o (e' + e'') :=: (e o e') + (e o e'')
                     leftdistr e e' e'' xs = part1 e e' e'' xs , part2 e e' e'' xs
                                             where
                                               part1 : forall e e' e'' xs -> xs <-[[ e o (e' + e'') ]] -> xs <-[[ (e o e') + (e o e'') ]]
                                               part1 e e' e'' xs (pr * (_ +> pr') <= eq) rewrite eq = _ +> pr * pr' <= refl
                                               part1 e e' e'' xs (pr * (_ <+ pr') <= eq) rewrite eq = _ <+ pr * pr' <= refl

                                               part2 : forall e e' e'' xs -> xs <-[[ (e o e') + (e o e'') ]] -> xs <-[[ e o (e' + e'') ]]
                                               part2 e e' e'' xs (_ <+ (pr * pr' <= eq)) rewrite eq = pr * (_ <+ pr') <= refl
                                               part2 e e' e'' xs (_ +> (pr * pr' <= eq)) rewrite eq = pr * (_ +> pr') <= refl

                     rightdistr : forall (e e' e'' : RegExp) -> ((e + e') o e'') :=: ((e o e'') + (e' o e''))
                     rightdistr e e' e'' xs = part1 e e' e'' xs , part2 e e' e'' xs
                                              where
                                                part1 : forall e e' e'' xs -> xs <-[[ (e + e') o e'' ]] -> xs <-[[ e o e'' + e' o e'' ]]
                                                part1 e e' e'' xs ((_ <+ pr) * pr' <= eq) rewrite eq = _ <+ (pr * pr' <= refl)
                                                part1 e e' e'' xs ((_ +> pr) * pr' <= eq) rewrite eq = _ +> (pr * pr' <= refl)

                                                part2 : forall e e' e'' xs -> xs <-[[ e o e'' + e' o e'' ]] -> xs <-[[ (e + e') o e'' ]]
                                                part2 e e' e'' xs (_ <+ (pr * pr' <= eq)) rewrite eq = (_ <+ pr) * pr' <= refl
                                                part2 e e' e'' xs (_ +> (pr * pr' <= eq)) rewrite eq = (_ +> pr) * pr' <= refl
                     open Semigroup
