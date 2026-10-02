-- Module      : Eser.Filters.Composition
-- Description : Composing Filters and properties of composition.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- Filter composition is NOT just pointwise ∧, as the ∧ of two dead-end-free
-- filters may very well have a dead end (i.e., be unsatisfiable, i.e., not
-- allowing *any choice* for some inputs).
--
-- However, we know that we can always take the congruence closure of a
-- relation. A relation R can be encoded as a filter F_R that allows only the
-- choices in R, so it is only satisfied by R.
-- We want to define a (non-symmetric) composition _»_ such that
-- F_R » P computes the P-closure of R (actually the filter that only allows
-- the relation that is the P-closure of R), where P is some dead-end-free
-- predicate like congruence.
--
-- We first adapt the definition of a Filter.
-- Instead of directly telling (via a Bool) for each choice of extending
-- an r : NFRestr n whether or not it is allowed, a Filter first tells whether
-- or not it 'fires' given r. If it fires, it behaves as usual.
-- If it doesn't fire (if it 'passes'), 
-- then we interpret that "every choice is OK, I don't care".
--
-- The composition G » F on input r returns (F r) : Choices r → Bool
-- if F fires on input r. If F passes on input r, but G fires on input r,
-- then we return (G r) : Choices r → Bool.
-- If both filters pass, then we accept all choices (so return (λ _ → true) :
-- Choices r → Bool).
--
-- This _»_ composition turns MayFireFilters into an idempotent non-commutative 
-- monoid, with the filter that always passes as unit.
-- The non-commutativity feels surprising, since combining predicates
-- on relations directly can be done via the commuting ∧,
-- but here the order does matter.
--
-- Note that passing is NOT the same as firing and then returning true on all
-- inputs, since passing goes to the next filter in the composition,
-- whereas firing gives a definite verdict on whether a choice is allowed.
-- Outside compositions, when the filter is used alone,
-- both options do behave identically though.
--------------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Data.Nat
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary
open import Data.Product
open import Data.Sum
open import Function using (_∘_ ; _$_)
--open import Data.Nat.Properties using 
--    (m<1+n⇒m<n∨m≡n 
--    ; n<1+n 
--    ; <-irrefl 
--    ; m≤n⇒m<n∨m≡n
--    ; <-trans
--    ; n≮n
--    ; <-irrelevant
--    ; suc-injective
--    ; ≤-refl
--    ; ≤-trans
--    ; n≤1+n
--    ; ≤-<-trans
--    )

--open import Eser.EqRel.Definitions using (NFFun ; DecEquiv)
--open import Eser.EqRel.Conversions using (RelToFun)
--open import Eser.Aux using (_↔_ ; _≈_ ; restIsProofIrrel ; n<1+n-lemma 
--    ; doubleSubst
--    ; m<1+n⇒m<n∨m≡n-when-≡
--    ; m<1+n⇒m<n∨m≡n-when-<
--    ; m≤n⇒m<n∨m≡n-when-<
--    )
--open import Data.Maybe

open import Eser.Filters.Base

module Eser.Filters.Composition where

--------------------------------------------------------------------------------
-- MayFireFilters
--------------------------------------------------------------------------------

-- Functor isomorphic to 'Maybe', but I use a different name to avoid confusion
-- with Maybe's well-known monadic Kleisli composition (which is NOT _»_
-- composition!).
data MayFire (A : Set) : Set where
    fire : A → MayFire A
    pass : MayFire A

MayFireFilter : Set
MayFireFilter = 
      {n : ℕ}
    → (r : NFRestr n)
    → MayFire(Choices r → Bool)

-- How we interpret a MayFireFilter as a Filter: passing means allowing all
-- choices.
MFF→Filter : MayFireFilter → Filter
MFF→Filter F {n} r c = cases (F r) c
    where
        cases : MayFire (Choices r → Bool) → Choices r → Bool
        cases (fire f) c = f c
        cases pass _ = true
