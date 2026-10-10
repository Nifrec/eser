-- Module      : Eser.EqRel.Definitions
-- Description : Representations of and predicates on equivalence relations.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------

{-# OPTIONS --safe #-}

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

module Eser.EqRel.Definitions where

--------------------------------------------------------------------------------
-- Relations on ℕ
--------------------------------------------------------------------------------
-- Relations as functions. 
-- This Bool-valued representation is always proof-irrelevant
-- and decidable, and more convenient when proving homotopy between relations.
-- The Agda stdlib lets a relation output a Set, which is annoying when
-- trying to show a homotopy that does not care about proof implementations.
DecRel : Set
DecRel = ℕ → ℕ → Bool

-- Decidable equivalence relations.
EqRel : Set
EqRel = Σ[ R ∈ DecRel ]( IsEquivalence (λ x y → R x y ≡ true))

_relates_to_ : EqRel → ℕ → ℕ → Set
(R , _) relates x to y = T (R x y)

-- R ⊆ S if S relates all pairs (x, y) that R relates.
_⊆_ : EqRel → EqRel → Set
R ⊆ S = ((x y : ℕ) → R relates x to y → S relates x to y)


--------------------------------------------------------------------------------
-- Normal-form functions and globally-defined properties of them.
--------------------------------------------------------------------------------
-- Coherence constraint on normal form functions: 
-- the normal form of n is always smaller or equal to n,
-- i.e., has been explored earlier.
-- This is necessary when building equivalence relations by inductively
-- assigning each n ∈ ℕ to its normal form.
NFLeq : (ℕ → ℕ) → Set
NFLeq f = (n : ℕ) → f n ≤ n

-- Coherence constraint on normal form functions: 
-- the normal form of a normal form is itself.
NFFix : (ℕ → ℕ) → Set
NFFix f = (n : ℕ) → f (f n) ≡ f n

-- Functions ℕ → ℕ that encode an equivalence relation,
-- i.e., functions that satisfy the coherence conditions that allow
-- them to be used as a normal-form function.
NFFun : Set
NFFun = Σ[ f ∈ (ℕ → ℕ) ]( NFLeq f × NFFix f)
