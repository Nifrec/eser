-- Module      : Eser.Signature.EnumOrderingProperties
-- Description : Lemmas about behaviour of AllTerms ≃ ℕ equivalence on orders.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- Lemmas about how the φ : AllTerms → ℕ equivalence
-- behaves w.r.t. the orders < and ≤ on ℕ and the corresponding
-- lifted orders « and «=.
--------------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Level
open import Data.Bool hiding (_≤_ ; _<_ ; _≤?_)
open import Data.Bool.Properties
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Induction
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding (J)
open import Relation.Nullary
open import Data.Product
open import Relation.Binary.Structures
open import Data.Fin hiding (_+_ ; _<_ ; _≤_)
open import Function
open import Relation.Binary.Reasoning.Syntax
open import Data.Fin.Properties using (fromℕ<-toℕ ; toℕ-fromℕ< ; toℕ-injective)

open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)

open import Eser.Card
open import Eser.Signature.Definitions
open import Eser.Signature.MainTheorem 
open import Eser.Signature.JumpEnum
open import Eser.Signature.Properties
open import Eser.Equivalences


module Eser.Signature.EnumOrderingProperties
    {μ' ζ' : ℕ∞} 
    (S : Signature (suc∞ μ') (suc∞ ζ'))
    where


import Eser.Signature.Recursion
-- This `open` defines, among other things, the equivalence φ : AllTerms S ~> ℕ:
open EquivShorthandsForEnumSet (infTermAlgEnum {μ'} {ζ'} S)

private
--    C : ℕ → Set
--    C = ClosedTerms {suc∞ μ'} {suc∞ ζ'} S
    OT : ℕ → ℕ → Set
    OT = OpenTerms {suc∞ μ'} {suc∞ ζ'} S

open Eser.Signature.MainTheorem.MainTheoremProof {μ'} {ζ'} S

-- If closed term t' has a lower weight than t
-- then φ(t') < φ(t) in ℕ.
smallerWeightSmallerIdx
    : {wₐ wₓ : ℕ}
    → (a : C wₐ)
    → (x : C wₓ)
    → wₐ < wₓ
    → (φ (wₐ , a)) < (φ (wₓ , x))

-- Corollary: giveArg t a always comes later in the enum than the argument a.
-- (We cannot say φ(t) < φ(giveArg t a) because t is strictly open
-- and φ is only defined on closed terms).
giveArgBigger
    : {wₐ wₜ : ℕ}
    → (a : C wₐ)
    → (t : OT wₜ 1)
    → (φ (wₐ , a)) < (φ (wₐ + wₜ , giveArg t a))


smallerWeightSmallerIdx {wₐ} {wₓ} a x wₐ<wₓ = ans
    where
        ------------------------------------------------------------------------
        -- Break down the equivalence φ : AllTerms S ~> ℕ
        -- into a composition of 3 equivalences.
        -- This follows the proof of `infTermAlgEnum` in
        -- `Eser.Signature.MainTheorem.
        ------------------------------------------------------------------------
        
        α : (Σ[ w ∈ ℕ ] C w) → (Σ[ i ∈ ℕ ] C (j i))
        α = ≃-to $ jumpOver⊥s C J ¬C0 a₀
        β : (Σ[ i ∈ ℕ ] C (j i)) → (Σ[ i ∈ ℕ ] (Fin $ ℕ.suc $ z i))
        β = ≃-to $ rewr-≃-rightOf-Σ $ Cw-to-Finz
        γ : (Σ[ i ∈ ℕ ] (Fin $ ℕ.suc $ z i)) → ℕ
        γ = ≃-to $ Σfin-inf-inhabited z
        
        check : φ ≡ γ ∘ β ∘ α
        check = refl

        -- Compute index of jump stops of a and x.
        -- Recall we jump from inhabited weight to the next inhabited weight,
        -- and since wₐ < wₓ, it must be that x lives in a later jump-stop than
        -- a.
        iₐ : ℕ
        iₐ = proj₁ $ α (wₐ , a)
        iₓ : ℕ
        iₓ = proj₁ $ α (wₓ , x)

        H₁ : iₐ < iₓ
        H₁ = jumpOver⊥s-mono C J ¬C0 a₀ {wₐ} {wₓ} a x wₐ<wₓ

        -- Our enumeration maps all inhabited sets of AllTerms of a given weight
        -- to a finite set. It does this for every jump stop,
        -- so now show that this preserves iₐ and iₓ.
        iₐ' : ℕ
        iₐ' = proj₁ $ β $ α (wₐ , a)
        H₂ : iₐ ≡ iₐ' 
        H₂ = refl

        iₓ' : ℕ
        iₓ' = proj₁ $ β $ α (wₓ , x)
        H₃ : iₓ ≡ iₓ' 
        H₃ = refl

        H₄ : iₐ' < iₓ'
        H₄ = H₁

        -- Finally, show that Σfin-inf-inhabited maps terms (i', t')
        -- with i' <ℕ i to a lower number than (i , t).
        ans : φ (wₐ , a) < φ (wₓ , x)
        ans = Σfin-inf-inhabited-mono z H₁ (proj₂ $ β $ α (wₐ , a)) 
                                           (proj₂ $ β $ α $ (wₓ , x))

giveArgBigger {wₐ} {wₜ} a t = smallerWeightSmallerIdx a x wₐ<wₓ
    where
        wₓ : ℕ
        wₓ = wₐ + wₜ

        x : C wₓ
        x = giveArg t a

        wₐ<wₓ : wₐ < wₐ + wₜ
        wₐ<wₓ = Data.Nat.Properties.m<m+n wₐ $ allTermsNonzeroWeight S t
