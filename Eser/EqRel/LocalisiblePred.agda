-- Module      : Eser.EqRel.LocalisiblePred
-- Description : Definition of localisible predicates
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- Predicates on relations, defined via a predicate on all finite
-- restrictions of a relation to a prefix of the underlying enumerated set.
--
-- This definition is not in Eser.EqRel.Definitions because it 
-- uses FunToRel defined in Eser.EqRel.Conversions,
-- which depends on Eser.EqRel.Definitions.
--------------------------------------------------------------------------------
open import Level
open import Data.Bool hiding (_≤_ ; _<_ ; _≤?_)
open import Data.Bool.Properties using (¬-not ; not-¬)
open import Data.Nat
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Relation.Binary.Structures
open import Data.Fin hiding (_≤_ ; _≤?_)
open import Data.Vec hiding (restrict)
open import Data.Nat.Properties using (≤-refl ; ≤-trans ; ≤-<-trans ; n≤0⇒n≡0 
                                       ; n≤1+n ; m≤n⇒m<n∨m≡n ; _≤?_ ; ≰⇒≥)
open import Data.Fin.Properties using (toℕ<n)
open import Relation.Nullary -- Needed for with-abstractions on decidable ≡.
open import Function hiding (_↔_)
open import Data.List hiding (lookup ; last)

open import Eser.Aux
open import Eser.Logic using (elimCaseLeft ; elimCaseRight)
open import Eser.EqRel.Definitions
open import Eser.EqRel.Conversions

module Eser.EqRel.LocalisiblePred where

--------------------------------------------------------------------------------
-- Localisible predicates
--
-- The intend is to capture the following:
-- a predicate of an equivalence relation on an enumerable set
-- A = {a₀, a₁, a₂, ...}
-- is 'localisible' if it is defined as an ℕ-indexed family of predicates
-- P that checks,
-- given a relation Rₙ₋₁ on [a₀, ..., aₙ₋₁] (that satisfies P)*
-- whether an extension of Rₙ₋₁ to Rₙ 
-- by choosing an equivalence class chosen for aₙ maintains P.
--
-- * In implementation we do not enforce this condition,
-- in the sense that we require that P holds 
-- on all restrictions of R to prefixes of A, not in any particular order.
--
-- Localisible predicates give a tool for building normalisation functions, 
-- and hence for building equivalence relations, 
-- and hence for building quotient types:
-- Start with the relation a₀ R a₀, i.e., with one equivalence class [a₀]
-- on the restriction {a₀}
-- and for each n ≥ 1, choose an equivalence class (either an existing class or
-- a new one) for aₙ, such that P still holds.
--
-- This is especially useful if it is hard to check P on a global relation
-- on ℕ (congruence, associativity, commutativity seem hard to define as a
-- function A → A → Bool!), 
-- but the local check on each {a₀, ..., aₙ} is decidable
-- (which in practise is often the case: checking 
-- if a finite equivalence relation
-- on the finite set {a₀, ..., aₙ} is congruent/associative/commutativity is
-- easy, just brute force!)
--------------------------------------------------------------------------------

-- A predicate P of equivalence relations on enumerable sets
-- that can be defined locally via a family {Pₙ}_{n ∈ ℕ} of predicates
-- for each restriction of the relation to a prefix of the set.
-- That is: P R =  ∧_{n ∈ N, R' = restriction R to {0, 1, ..., n-1}} Pₙ R'
-- (for all decidable R ⊆ ℕ × ℕ).
record LocalisiblePred : Set₁ where
    constructor localisiblePred
    field
        Prel : RelPred
        Ploc : LocPred
        correspondence : 
            (R : DecEquiv) → (Prel R ↔ (AllRestr (proj₁ (RelToFun R)) Ploc))
open LocalisiblePred

-- A local predicate that is pointwise decidable.
DecLocPred : LocPred → Set
DecLocPred P = (n : ℕ) → (v : Vec ℕ n) → Dec (P n v)

-- A localisible predicate whose local restrictions Pₙ are all decidable.
LocallyDecPred : Set₁
LocallyDecPred = Σ[ P ∈ LocalisiblePred ](DecLocPred (Ploc P))
