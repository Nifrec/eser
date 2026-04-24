-- Module      : Eser.Signature.Recursion
-- Description : Well-founded recursion on terms of a signature.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- One can define functions out of the terms of a signature by recursion
-- on 'smaller' terms. A term t' is smaller than t when, in the enumeration
-- of terms, t' comes before t.
-- We just lift <-rec on ℕ via the equivalence AllTerms ≃ ℕ.
--
-- #EXT: currently only implemented for signatures with infinitely many terms.
--       Can be generalised to also allow signatures with finitely many terms.

open import Level
open import Data.Bool hiding (_≤_ ; _<_ ; _≤?_)
open import Data.Bool.Properties
open import Data.Nat hiding (_/_)
open import Data.Nat.Properties
open import Data.Nat.Induction
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Relation.Binary.Structures
open import Data.Fin hiding (_+_ ; _<_ ; _≤_)
open import Data.Vec 
open import Function
open import Relation.Binary.Reasoning.Syntax
open import Data.Fin.Properties using (fromℕ<-toℕ ; toℕ-fromℕ< ; toℕ-injective)

open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)

open import Eser.Card
open import Eser.Equivalences.Notation
open import Eser.Equivalences.Properties
open import Eser.Aux
open import Eser.Signature
open import Eser.EqRel
open import Eser.Quotient.Definitions

module Eser.Signature.Recursion 
    {μ' ζ' : ℕ∞} 
    (S : Signature (suc∞ μ') (suc∞ ζ'))
    where

μ = suc∞ μ'
ζ = suc∞ ζ'  

-- All terms of S.
𝕋 : Set
𝕋 = AllTerms {μ} {ζ} S

𝕋≃ℕ : 𝕋 ≃ ℕ
𝕋≃ℕ = infTermAlgEnum {μ'} {ζ'} S

φ : 𝕋 → ℕ
φ = ≃-to 𝕋≃ℕ

φ⁻¹ : ℕ → 𝕋
φ⁻¹ = ≃-from 𝕋≃ℕ

φ∘φ⁻¹≈id : (φ ∘ φ⁻¹) ≈ id
φ∘φ⁻¹≈id = ≃-toFrom 𝕋≃ℕ

φ⁻¹∘φ≈id : (φ⁻¹ ∘ φ) ≈ id
φ⁻¹∘φ≈id = ≃-fromTo 𝕋≃ℕ

-- Smaller-term relation: the ℕ-encoding of t' is ℕ-< smaller than t.
_«_ : Rel (AllTerms {μ} {ζ} S) 0ℓ
t' « t = (φ t') < (φ t)

-- Well-founded recursion on the «-relation.
-- It lifts well-founded recursion on (ℕ , <) via the
-- (φ , φ⁻¹) : T ≃ ℕ equivalence.
«-rec
    : {P : 𝕋 → Set}
    → ( (t : 𝕋) → ((t' : 𝕋) → (t' « t) → P t') → P t)
    → (t : 𝕋) → P t
«-rec {P} H t = substInv t $ <-rec {0ℓ} (P ∘ φ⁻¹) H' (φ t)
    where
        substInv : (t : 𝕋) → (P $ φ⁻¹ $ φ $ t) → P t
        substInv t Pt = subst P (φ⁻¹∘φ≈id t) Pt
        H' : (n : ℕ) → ({m : ℕ} → (m < n) → P (φ⁻¹ m)) → P (φ⁻¹ n)
        H' n rec = H (φ⁻¹ n) rec'
            where
                rec' : (t' : 𝕋) → (t' « (φ⁻¹ n)) → P t'
                rec' t' t'«φ⁻¹n = substInv t' (rec {φ t'} k)
                    where
                        k : φ t' < n
                        k = subst (λ x → φ t' < x) (φ∘φ⁻¹≈id n) t'«φ⁻¹n
