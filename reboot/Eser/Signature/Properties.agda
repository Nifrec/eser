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

module _ 
    {μ ζ : ℕ∞} 
    (S : Signature μ ζ) 
    where
    -- The number of open argument-holes in a term is bounded by the 
    -- arities of the constructors.
    -- No term has more holes than any constructor.
    -- Intuitively obvious, since every term is ultimately a constructor 
    -- with zero or more aguments applied.
    -- Implementation: Well-founded recursion on weights.
    holesBoundedByArity
        : {w : ℕ}
        → (n : ℕ)
        → (x : OpenTerms {μ} {ζ} S w (ℕ.suc n)) 
            --^ Existence of term with 1+n holes.
        → Σ[ c ∈ cardToSet ζ ] (ℕ.suc n ≤ arity {μ} {ζ} {S} c)
    holesBoundedByArity {w} n x = <-rec P holesBoundedByArityRec w n x
        where
            P : ℕ → Set
            P w = (n : ℕ) 
                  → (x : OpenTerms {μ} {ζ} S w (ℕ.suc n))
                  → Σ[ c ∈ cardToSet ζ ] (ℕ.suc n ≤ arity {μ} {ζ} {S} c)
            holesBoundedByArityRec : (w : ℕ) → ({v : ℕ} → v < w → P v) → P w
            holesBoundedByArityRec w rec n (mk-multiary c) = 
                (c ,  Data.Nat.Properties.≤-refl )
            holesBoundedByArityRec w rec n (giveArg {wₜ} {wₐ} t a) = (c , ans)
                where
                    wₜ<w : wₜ < w
                    wₜ<w = subst (λ y → wₜ < y) (+-comm wₜ wₐ)
                           $ Data.Nat.Properties.m<m+n wₜ 
                           $ allTermsNonzeroWeight S a
                    c : cardToSet ζ
                    c = proj₁ $ rec {wₜ} wₜ<w (ℕ.suc n) t
                    p : ℕ.suc (ℕ.suc n) ≤ arity {μ} {ζ} {S} c
                    p = proj₂ $ rec {wₜ} wₜ<w (ℕ.suc n) t
                    ans : ℕ.suc n ≤ arity {μ} {ζ} {S} c
                    ans = Data.Nat.Properties.≤-trans (n≤1+n $ ℕ.suc n) p
            
