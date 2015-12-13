open import Data.List as List
open import Data.List.Properties
open List-solver renaming (nil to :[] ; _⊕_ to _:++_; _⊜_ to _:==_)
open import Data.Product renaming (_×_ to _*_)

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

  -- lemma choice idempotent

  lemChoiceIdem : (e : RegExp) -> (e + e) :=: e
  lemChoiceIdem e xs = part1 xs e , part2 xs e
                       where
                         part1 : forall xs e -> xs <-[[ e + e ]] -> xs <-[[ e ]]
                         part1 _ e' (.e' <+ pr) = pr
                         part1 _ e' (.e' +> pr) = pr

                         part2 : forall xs e -> xs <-[[ e ]] -> xs <-[[ e + e ]]
                         part2 .[] .Eps Eps = Eps <+ Eps
                         part2 .(a ∷ []) .(# a) (# a) = # a <+ # a
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


  -- lemma concatenation empty

  lemConcatEmpL : (e : RegExp) -> (Emp o e) :=: Emp
  lemConcatEmpL e xs = part1 xs e , part2 xs e
                       where
                         part1 : forall xs e -> xs <-[[ Emp o e ]] -> xs <-[[ Emp ]]
                         part1 xs e (() * pr' <= eq)

                         part2 : forall xs e -> xs <-[[ Emp ]] -> xs <-[[ Emp o e ]]
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

  -- star kleene choice and concat

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
                      part2 xs e ((_ +> (pr * pr' <= eq)) *) rewrite eq = {!(lemChoiceEmpL (lemChoiceComm e) xs) * ? <= ?!}
                      part2 xs e ((_ <+ pr) *) = (_ <+ pr) *
