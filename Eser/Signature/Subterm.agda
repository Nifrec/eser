-- Module      : Eser.Signature.Subterm
-- Description : Subterm relation and theorem subterms-smaller-in-enumeration.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- This file shows that arguments of closed terms, or arguments to argument, or
-- ..., always come earlier in the enumeration than the big term itself.
--------------------------------------------------------------------------------
open import Level
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Relation.Binary.Structures
open import Function
open import Relation.Binary.Reasoning.Syntax

open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)

open import Eser.Card
open import Eser.Signature.Definitions


module Eser.Signature.Subterm where

module SubtermDef
    {μ ζ : ℕ∞} 
    (S : Signature μ ζ) 
    where

    private
        OT = OpenTerms {μ} {ζ} S

    -- Design remark: we could also have used:
    -- ⋤-recurse : (a' ⋤ t) → (a' ⋤ giveArg t a)
    -- instead of ⋤-base.
    -- Then the subterms are only arguments, not
    -- the-same-term-but-with-some-arguments-removed.
    -- However, defining ⋤ to be a larger relation is both simpler
    -- and yields an equally strong subterm-earlier-in-enum theorem.
    -- (the restrictions to closed terms are the same, 
    -- regardless of using ⋤-recurse or ⋤-base).
    data _⋤_ : {w w' n n' : ℕ} → OT w n → OT w' n' → Set where
        ⋤-arg 
            : {wₜ wₐ n : ℕ} 
            → (t : OT wₜ (ℕ.suc n)) 
            → (a : OT wₐ 0) 
            → a ⋤ giveArg t a
        ⋤-base 
            : {wₜ wₐ n : ℕ} 
            → (t : OT wₜ (ℕ.suc n)) 
            → (a : OT wₐ 0) 
            → t ⋤ giveArg t a
        ⋤-trans 
            : {w₁ w₂ w₃ n₁ n₂ n₃ : ℕ} 
            → {t₁ : OT w₁ n₁}
            → {t₂ : OT w₂ n₂}
            → {t₃ : OT w₃ n₃}
            → t₁ ⋤ t₂
            → t₂ ⋤ t₃
            → t₁ ⋤ t₃

module _ {μ' ζ' : ℕ∞} (S : Signature (suc∞ μ') (suc∞ ζ'))
    where

    open import Eser.Signature.MainTheorem using (infTermAlgEnum)
    open import Eser.Signature.Properties
    open import Eser.Equivalences.Notation

    private
        μ = suc∞ μ'
        ζ = suc∞ ζ'
        OT = OpenTerms {μ} {ζ} S
        C : ℕ → Set
        C = λ w → OpenTerms {μ} {ζ} S w 0
        𝕋 = AllTerms {μ} {ζ} S
        𝕋≃ℕ = infTermAlgEnum {μ'} {ζ'} S

    open SubtermDef {μ} {ζ} S

    open import Eser.Signature.EnumOrderingProperties {μ'} {ζ'} S
        
    subterm-smaller-weight
        : {w w' n n' : ℕ}
        → {t : OT w n}
        → {t' : OT w' n'}
        → (t' ⋤ t)
        → w' < w
    subterm-smaller-weight {w} {w'} {n} {n'} {giveArg t' a} {a} (⋤-arg t' a)
        = giveArgSmallerWeight-right S t' a
    subterm-smaller-weight {w} {w'} {n} {n'} {giveArg t' a} {t'} (⋤-base t' a)
        = giveArgSmallerWeight-left S t' a
    subterm-smaller-weight {w} {w'} {t} {t'} (⋤-trans {w'} {w₁} {w} t'⋤t₁ t₁⋤t)
        = <-trans w'<w₁ w₁<w
        where
            w'<w₁ : w' < w₁
            w'<w₁ = subterm-smaller-weight t'⋤t₁
            w₁<w : w₁ < w
            w₁<w = subterm-smaller-weight t₁⋤t

    -- This imports the earlier-in-enum-relation `_«_`:
    open EquivShorthandsForEnumSet {𝕋} 𝕋≃ℕ

    subterm-earlier-in-enum
        : {w w' : ℕ}
        → {t : C w}
        → {t' : C w'}
        → (t' ⋤ t)
        → (w' , t') « (w , t)
    subterm-earlier-in-enum {w} {w'} {t} {t'} t'⋤t 
        = smallerWeightSmallerIdx t' t w'<w
        where
            w'<w : w' < w
            w'<w = subterm-smaller-weight t'⋤t
