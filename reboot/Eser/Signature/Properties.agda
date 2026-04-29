-- Module      : Eser.Signature.Properties
-- Description : Basic properties of term algebras over signatures.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------

-- #TODO: remove unused imports
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
open import Function
open import Relation.Binary.Reasoning.Syntax
open import Data.Fin.Properties using (fromℕ<-toℕ ; toℕ-fromℕ< ; toℕ-injective)

open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)

open import Eser.Card
open import Eser.Signature.Definitions

module Eser.Signature.Properties where

openTermsEquality
    : {μ ζ : ℕ∞}
    → (S : Signature μ ζ)
    → {w n : ℕ}
    → {t t' : OpenTerms {μ} {ζ} S w n}
    → _≡_ {A = Σ[ w ∈ ℕ ](OpenTerms {μ} {ζ} S w n)} (w , t) (w , t')
    -- ^ Just (w , t) ≡ (w , t'). Agda needed some help finding the base type.
    → t ≡ t'
openTermsEquality S refl = refl

openTermsEqualityW&N
    : {μ ζ : ℕ∞}
    → (S : Signature μ ζ)
    → {w n : ℕ}
    → {t t' : OpenTerms {μ} {ζ} S w n}
    → _≡_ {A = Σ[ w ∈ ℕ ] Σ[ n ∈ ℕ ](OpenTerms {μ} {ζ} S w n)} 
          (w , n , t) (w , n , t')
    -- ^ Just (w , n , t) ≡ (w , n , t'). 
    -- Agda needed some help finding the base type.
    → t ≡ t'
openTermsEqualityW&N S refl = refl

-- Every open term has weight at least 1, which follows
-- directly from the constructors of OpenTerms.
allTermsNonzeroWeight
    : {μ ζ : ℕ∞} 
    → (S : Signature μ ζ) 
    → {w n : ℕ}
    → OpenTerms {μ} {ζ} S w n
    → 0 < w
allTermsNonzeroWeight {μ} {ζ} S {w} {n} (mk-nullary c) = s≤s z≤n
allTermsNonzeroWeight {μ} {ζ} S {w} {n} (mk-multiary c) = s≤s z≤n
allTermsNonzeroWeight {μ} {ζ} S {w} {n} (giveArg {wₜ} {wₐ} t a) = 
    let 0<wₐ : 0 < wₐ
        0<wₐ = allTermsNonzeroWeight S a
    in
    <-≤-trans 0<wₐ (m≤m+n wₐ wₜ)

-- No terms with weight 0 exist; all terms have at least weight 1.
noWeightlessTerms 
    : {μ ζ : ℕ∞} 
    → (S : Signature μ ζ) 
    → (n : ℕ)
    → OpenTerms {μ} {ζ} S 0 n
    → ⊥ 
noWeightlessTerms {μ} {ζ} S n t = n≮0 $ allTermsNonzeroWeight S t

