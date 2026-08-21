-- Module      : Eser.Filters.ReplaceStructs.ForSignature
-- Description : All signatures have the structure of a ReplaceStruct.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- Only for signatures with infinite term algebras (equivalent to ℕ)
-- (and with at least one multiarty constructor).

open import Data.Nat
open import Data.Bool hiding (_<_ ; _≤_ ; _≟_ ; _≤?_ )
open import Data.Bool.Properties using (T-≡)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open ≡-Reasoning
open import Relation.Nullary
open import Relation.Binary.Definitions using (Decidable ; DecidableEquality 
    ; tri< ; tri≈ ; tri>)
open import Data.Product
open import Data.Sum
open import Function using (_∘_ ; _$_ ; id)

open import Data.Nat.Properties using (
    ≤-refl 
    ; ≤-trans 
    ; <-trans
    ; n≤1+n 
    ; ≡⇒≡ᵇ
    ; <-irrelevant
    ; n<1+n
    ; n≮0
    ; <-≤-trans
    ; ≤-<-trans
    ; m≤n⇒m<n∨m≡n
    ; n≮n
    ; ≰⇒>
    )

open import Eser.EqRel.Definitions using (NFFun ; DecEquiv)
open import Eser.EqRel.Conversions using (RelToFun ; FunToRel)
open import Eser.Aux using (_↔_ ; _≈_ ; doubleSubst ; irrel-×-closure ; uip
    ; restIsProofIrrel
    )
open import Eser.Logic using 
    (true≢false 
    ; ≡→≡ᵇ 
    ; ≡ᵇ→≡ 
    ; decEqReflection
    ; decEqCoReflection
    ; is-false-to-not-true
    ; not-true-to-is-false
    )

open import Eser.Filters.Base
open import Eser.Filters.Properties
open import Eser.Filters.Resurface
open import Eser.Filters.PointwiseProperties
open import Eser.Filters.Conversions.NFFunToExence
open import Eser.Filters.ReplaceStructs

open import Eser.Signature.Definitions
open import Eser.Signature.MainTheorem
open import Eser.Card
open import Eser.Equivalences
open import Eser.Equivalences.Notation

open ReplaceStruct

module Eser.Filters.ReplaceStructs.ForSignature 
    {μ : ℕ∞} {ζ : ℕ∞} (S : Signature (suc∞ μ) (suc∞ ζ)) where
    -- Implementation note: we are using the version with weight annotations
    -- because this will make it much easier to prove how replacement of an
    -- argument by a smaller argument leads to a smaller term.
    C = ClosedTerms {suc∞ μ} {suc∞ ζ} S
    OT = OpenTerms {suc∞ μ} {suc∞ ζ} S

    -- Is-an-argument-of-relation.
    -- Not to be confused with the 'subterm' relation in Eser.Signature.Subterm.
    -- The latter relation is transitive and also relates
    -- t to `giveArg t a`, while t is not an argument.
    data _⋤_ : {n n' w w' : ℕ} → OT w n → OT w' n' → Set where
        here 
            : {n wₜ wₐ : ℕ} 
            → (t : OT wₜ (ℕ.suc n)) 
            → (a : OT wₐ 0) 
            → a ⋤ giveArg t a
        earlier 
            : {n wₜ wₐ wₐ' : ℕ} 
            → (t : OT wₜ (ℕ.suc n)) 
            → (a : OT wₐ 0) 
            → (a' : OT wₐ' 0) 
            → a ⋤ t
            → a ⋤ giveArg t a'

    -- Replacement of arguments defined on Open Terms.
    -- The enumeration bijection will allow to lift this from OT to ℕ.
    OT-replace 
        : {n wₜ wₐ wₐ' : ℕ} 
        → (t : OT wₜ n) 
        → (a : OT wₐ 0) 
        → (a' : OT wₐ' 0) 
        → a ⋤ t 
        --^ Implies wₜ > wₐ, so wₜ ∸ wₐ will be nonzero.
        --  Can be proven using `subterm-smaller-weight` in Signature.Subterm.
        → Σ[ w' ∈ ℕ ] Σ[ t' ∈ OT w' n ] (a' ⋤ t) × (w' ≡ (wₜ + wₐ') ∸ wₐ)
    OT-replace t a a' = ?

    𝕋 : Set
    𝕋 = AllTerms {suc∞ μ} {suc∞ ζ} S

    𝕋≃ℕ = infTermAlgEnum {μ} {ζ} S
    --open EquivShorthandsForEnumSet 𝕋≃ℕ
    φ : 𝕋 → ℕ
    φ = ≃-to 𝕋≃ℕ
    φ⁻¹ : ℕ → 𝕋
    φ⁻¹ = ≃-from 𝕋≃ℕ
    φ∘φ⁻¹≈id : (φ ∘ φ⁻¹) ≈ id
    φ∘φ⁻¹≈id = ≃-toFrom 𝕋≃ℕ
    φ⁻¹∘φ≈id : (φ⁻¹ ∘ φ) ≈ id
    φ⁻¹∘φ≈id = ≃-fromTo 𝕋≃ℕ

    -- #TODO: if `a` doesn't occur in t then return t unchanged.
    -- So add a case distinction!
    sig-replace : ℕ → ℕ → ℕ → ℕ
    sig-replace t a a' = 
        let (w' , t' , _) = OT-replace (proj₂ $ φ⁻¹ t) (proj₂ $ φ⁻¹ a) 
                                       (proj₂ $ φ⁻¹ a') ?
        in
        φ (w' , t')

    -- Extract underlying replacement structure from a Signature.
    toReplaceStruct : ReplaceStruct
    toReplaceStruct ._is-arg-of_ = {! !}
    toReplaceStruct .⊂-resp-< = {! !}
    toReplaceStruct .replace = {! !}
    toReplaceStruct .replace-< = {! !}
    toReplaceStruct .keep y x x' z x₁ x₂ x₃         = {! !}
    toReplaceStruct .nospawn y x x' z x₁ x₂         = {! !}
    toReplaceStruct .comm y x x' z z' x₁ x₂ x₃ x₄   = {! !}
    toReplaceStruct .noeff y x x' x₁                = {! !}
    toReplaceStruct .halfcut y x z a                = {! !}
    toReplaceStruct .id-rep y x                     = {! !}
    toReplaceStruct .complete y x x' x₁ x₂          = {! !}

    ----------------------------------------------------------------------------
    -- 𝟓. Familiar definition of congruence
    ----------------------------------------------------------------------------
    -- Is-an-argument-of-relation, lifted to ℕ via the bijection φ : 𝕋 ≃ ℕ.
    _⋤ℕ_ : ℕ → ℕ → Set
    t ⋤ℕ a = (proj₂ $ φ⁻¹ t) ⋤ (proj₂ $ φ⁻¹ a)

    IsCongruence : DecEquiv → Set
    IsCongruence R'@(R , is-equiv-rel) 
        = (t : ℕ)                         --^ For all closed terms t ...
        → (a : ℕ) → (a ⋤ℕ t)              --^ ... and all arguments a of t
        → (a' : ℕ)                        --^ ... and all alternatives a'
        → R a a' ≡ true                   --^     that are related to a
        → R t (sig-replace t a a') ≡ true --^ t and t[a'/a] must be related.
