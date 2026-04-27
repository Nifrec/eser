-- Module      : Eser.Signature.NoWeights
-- Description : Properties of the NoWeight representation of open terms.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- Properties shown:
-- 1. Decidable equality between open terms.
-- 2. Equivlance to the weight-annotated representation to open terms.

{-# OPTIONS --allow-unsolved-metas #-}

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
open import Eser.Signature.Definitions
open import Eser.Signature.MainTheorem
open import Eser.Signature.NoWeight.Definitions
open import Eser.Equivalences
open import Eser.Aux

module Eser.Signature.NoWeight.Properties where

module _ {μ ζ : ℕ∞} (S : Signature μ ζ) where
    private
        CNW : Set
        CNW = ClosedTermsNW {μ} {ζ} S

        OT : ℕ → ℕ → Set
        OT = OpenTerms {μ} {ζ} S

        OTNW : ℕ → Set
        OTNW = OpenTermsNW {μ} {ζ} S

    -- Equality between open terms is decidable.
    decEquality : {n : ℕ} → (t t' : OTNW n) → Relation.Nullary.Dec (t ≡ t')
    decEquality = ?

    ----------------------------------------------------------------------------
    -- Recomputing the weights
    --
    -- The weights are really just annotations.
    -- Every term has exacly one weight.
    -- So we obtain a bijection between OpenTermsNW and OpenTerms
    ----------------------------------------------------------------------------

    -- Weights are computed the same way as the indices in OpenTerms.
    weight : {n : ℕ} → OTNW n → ℕ
    weight (mk-nullary-nw c) = (ℕ.suc $ cardToℕ c)
    weight (mk-multiary-nw c) = (ℕ.suc $ cardToℕ c)
    weight (giveArg-nw t a) = weight a + weight t

    -- The weight function allows to embed OpenTermsNW into OpenTerms,
    -- and the forgetful function gives an inverse map to it.
    forgetWeight : {w n : ℕ} → OT w n → OTNW n
    forgetWeight {w} {n} (mk-nullary c) = mk-nullary-nw c
    forgetWeight {w} {n} (mk-multiary c) = mk-multiary-nw c
    forgetWeight {w} {n} (giveArg t a) = giveArg-nw t' a'
        where
            t' = forgetWeight t
            a' = forgetWeight a

    -- Uncurried version of the above.
    forgetWeight' : {n : ℕ} → Σ[ w ∈ ℕ ](OT w n) → OTNW n
    forgetWeight' {n} (w , t) = forgetWeight {w} {n} t

    addWeight : {n : ℕ} → OTNW n → Σ[ w ∈ ℕ ](OT w n)
    addWeight {n} t@(mk-nullary-nw c) = (weight t , mk-nullary c)
    addWeight {n} t@(mk-multiary-nw c) = (weight t , mk-multiary c)
    addWeight {n} t@(giveArg-nw t₀ a) = (wₐ + wₜ₀ , giveArg t₀' a')
        where
            wₜ₀ = proj₁ $ addWeight t₀
            t₀' = proj₂ $ addWeight t₀
            wₐ = proj₁ $ addWeight {0} a
            a' = proj₂ $ addWeight {0} a

    proj₁AddWeight
        : {n : ℕ}
        → (proj₁ ∘ addWeight {n}) ≈ weight {n}
    proj₁AddWeight {n} (mk-nullary-nw c) = refl
    proj₁AddWeight {n} (mk-multiary-nw c) = refl
    proj₁AddWeight {n} (giveArg-nw t a) = 
        ≡begin 
            (proj₁ $ addWeight $ giveArg-nw t a)
        ≡⟨⟩
            (proj₁ $ addWeight a) + (proj₁ $ addWeight t)
        ≡⟨ cong (λ w → (proj₁ $ addWeight a) + w) (proj₁AddWeight t) ⟩
            (proj₁ $ addWeight a) + weight t
        ≡⟨ cong (λ w → w + weight t) (proj₁AddWeight a) ⟩
            weight a + weight t
        ≡⟨⟩
            weight (giveArg-nw t a)
        ≡∎

    weightRecover
        : {w n : ℕ}
        → (t : OT w n)
        → weight (forgetWeight' {n} (w , t)) ≡ w
    weightRecover {w} {n} t = ?

    OTequiv
        : {n : ℕ} 
        → (OTNW n) ≃ (Σ[ w ∈ ℕ ] (OT w n))

    OTequiv {n} = mk≃' addWeight forgetWeight' invˡ invʳ
        where
        invˡ : Inverseˡ _≡_ _≡_ addWeight forgetWeight'
        invˡ {w , mk-nullary c} {y} refl = refl
        invˡ {w , mk-multiary c} {y} refl = refl
        invˡ {w , giveArg {wₜ} {wₐ} t a} {y} refl = 
            let tNW = forgetWeight' (wₜ , t) in
            let aNW = forgetWeight' (wₐ , a) in
            let t' = (proj₂ $ addWeight $ forgetWeight' (wₜ , t)) in
            let wₜ' = (proj₁ $ addWeight $ forgetWeight' (wₜ , t)) in
            let a' = (proj₂ $ addWeight $ forgetWeight' (wₐ , a)) in
            let wₐ' = (proj₁ $ addWeight $ forgetWeight' (wₐ , a)) in
            let H : wₜ' ≡ wₜ
                H = trans (proj₁AddWeight $ forgetWeight' (wₜ , t)) (weightRecover t)
            in
            ≡begin 
                addWeight (forgetWeight' (wₐ + wₜ , giveArg t a))
            ≡⟨⟩
                addWeight (giveArg-nw (forgetWeight' (wₜ , t)) 
                                      (forgetWeight' (wₐ , a))
                          )
            ≡⟨⟩
                ((proj₁ $ addWeight aNW) + (proj₁ $ addWeight tNW) , giveArg t' a')
            ≡⟨ ? ⟩
                -- #TODO: use H above. Also make a Hₐ.
                -- Second projections should use substitutions...
                -- Maybe prove strict inversity.
                -- **Or prove injectivity & surjectivity.**
                (wₜ + wₐ , {! giveArg t' a'!} )
            ≡⟨ ? ⟩
                (wₐ + wₜ , giveArg t a) 
            ≡∎
            --where
            --    t' = forgetWeight' (wₜ , t)
            --    (wₜ'' , t'') = addWeight t'
                
                --P₁AWₜ = proj₁ $ addWeight t
                --t' = proj₂ $ addWeight t
                --P₁AWₐ = proj₁ $ addWeight {0} a
                --a' = proj₂ $ addWeight {0} a
            
        invʳ : Inverseʳ _≡_ _≡_ addWeight forgetWeight'
        invʳ {mk-nullary-nw c} {x} refl = refl
        invʳ {mk-multiary-nw c} {x} refl = refl
        invʳ {giveArg-nw t a} {x} refl = {! !}

-- Corollary: the no-weight closed terms of a signature can be enumerated,
-- because the weight-annotated closed terms can.
infTermAlgEnumNW
    : {μ ζ : ℕ∞}
    → (S : Signature (suc∞ μ) (suc∞ ζ))
    → (ClosedTermsNW {suc∞ μ} {suc∞ ζ} S) ≃ ℕ
infTermAlgEnumNW {μ} {ζ} S = ≃-trans CTNW≃AT AT≃ℕ
    where
        μ' = suc∞ μ
        ζ' = suc∞ ζ
        CTNW≃AT : ClosedTermsNW {μ'} {ζ'} S ≃ AllTerms {μ'} {ζ'} S
        CTNW≃AT = OTequiv {μ'} {ζ'} S {0}

        AT≃ℕ : AllTerms {μ'} {ζ'} S ≃ ℕ
        AT≃ℕ = infTermAlgEnum {μ} {ζ} S
