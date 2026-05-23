-- Module      : Eser.Unions
-- Description : Equivalences between certain infinite disjoined unions
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
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

open import Eser.Logic using (elimCaseLeft ; elimCaseRight)
--open import Relation.Nullary
--open ≡-Reasoning
--open import Data.Nat.Properties
--open import Data.Fin
--open import Data.Fin.Properties
--open import Data.Fin.Induction
--open import Data.Empty
--open import Data.List
--open import Data.List.Relation.Unary.AllPairs using (AllPairs)
--open import Data.List.Relation.Unary.All using (All)
--open import Data.List.Relation.Binary.Suffix.Heterogeneous using (Suffix)
--open import Data.List.Membership.Propositional using (_∈_ ; _∉_ )
--open import Data.List.Membership.Propositional.Properties using (∈-lookup)
--open import Data.List.Relation.Unary.Any using (Any)

open import Eser.Definitions using (_≈_)

module Eser.Unions where

-- Equivalence between two types.
-- The stdlib uses an overly general definition
-- what requires also showing `n ≈₁ m → (f n) ≈₂ (f m)`
-- given setoids (N, ≈₁) and (M, ≈₂).
-- We just use propositional equality _≡_ for both the domain and codomain,
record HomotEquivalence (Left Right : Set) : Set where 
    field
        LR : Left → Right
        RL : Right → Left
        homotLRL : (RL ∘ LR) ≈ id
        homotRLR : (LR ∘ RL) ≈ id

_≃_ : Set → Set → Set
A ≃ B = HomotEquivalence A B

-- An infinite union of non-empty finite sets
data ∞∐ (sizes : ℕ → ℕ) : Set
    where
        ∞inj 
            : (n : ℕ)                 -- Index of finite set in the union.
            → (Fin (ℕ.suc (sizes n))) -- Index of number within the finite set.
            → ∞∐ sizes

-- A finite union of non-empty finite sets
data ∐ (m : ℕ) (sizes : Fin m → ℕ) : Set
    where
        inj
            : (i : Fin m)             -- Index of finite set in the union.
            → (Fin (ℕ.suc (sizes i))) -- Index of number within the finite set.

∞Squash : (sizes : ℕ → ℕ) → (∞∐ sizes) ≃ ℕ
∞Squash sizes = (f , g , gfHomot , fgHomot)
    where
        f : ∞∐ sizes → ℕ
        f = ?
        g : ℕ → ∞∐ sizes
        g = ?
        gfHomot : g ∘ f ≈ id
        gfHomot = ?
        fgHomot : f ∘ g ≈ id
        fgHomot = ?
