-- Module      : Eser.Monotone
-- Description : Basic definitions and properties of funs monotone on (ℕ, <).
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- Most things could have been defined much more general,
-- e.g., for all total orders on any type,
-- but within Eser we only need it for ℕ → ℕ functions.
-- It is possible that all the results in here are in some abstract/generalised
-- form in the stdlib, but I haven't been able to find them.


{-# OPTIONS --allow-unsolved-metas #-}

open import Level
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
open import Relation.Unary
open import Data.Product
open import Relation.Binary.Structures
open import Function
open import Relation.Binary.Reasoning.Syntax

open import Eser.Aux

open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)

module Eser.Monotone where

-- Functions f : ℕ → ℕ such that (m < n) ⇒ (f m < f n).
ℕ<Monotone : (ℕ → ℕ) → Set 
ℕ<Monotone = Monotonic₁ _<_ _<_

-- Functions injective on ℕ.
ℕInjective : (ℕ → ℕ) → Set
ℕInjective = Injective _≡_ _≡_


piecewiseIncrImplMonoLemma
    : {f : ℕ → ℕ}
    → ((n : ℕ) → f n < f (ℕ.suc n))
    → ((n k : ℕ) → f n < f (ℕ.suc k + n))
piecewiseIncrImplMonoLemma {f} H n k = 
    ?
    where
        -- #TODO: refactor to somewhere else
        lemma : {m n : ℕ} → m < n → Σ[ k ∈ ℕ ] n ≡ k + m
        lemma {0} {n} (s≤s z≤n) = (n , sym ( +-identityʳ n))
        lemma {suc m} {suc (suc n)} (s≤s (s≤s m<n)) = 
            let (k' , n≡k'+m) = lemma (s≤s m<n)
            in
            (ℕ.suc k' , ? ) -- (subst (λ x → n ≡ x) (+-suc k' m) n≡k'+m))

-- If f (suc n) > f n for all n, then that already implies that
-- f is monotone.
piecewiseIncrImplMono
    : {f : ℕ → ℕ}
    → ((n : ℕ) → f n < f (ℕ.suc n))
    → ℕ<Monotone f
piecewiseIncrImplMono {f} H {m} {n} (s≤s z≤n) = {! !}
piecewiseIncrImplMono {f} H {m} {n} (s≤s (s≤s m<n)) = {! !}

monotoneImplInjective
    : {f : ℕ → ℕ}
    → ℕ<Monotone f
    → ℕInjective f
monotoneImplInjective {f} H = ?

-- If f : ℕ → ℕ is strictly increasing,
-- then it factorises most of ℕ into the intervals
-- [f 0 , f 1) [f 1 , f2) [f 2 , f 3) , ...
-- and any number w ≥ f 0 falls into exactly one such interval.
increasingImplIval
    : (f : ℕ → ℕ)
    → Monotonic₁ _<_ _<_ f -- ((n : ℕ) → f n < f (ℕ.suc n))
    → (w : ℕ)
    → f 0 ≤ w
    → Σ[ i ∈ ℕ ]( f i ≤ w × w < f (ℕ.suc i))
increasingImplIval f mono w f0≤w = ?

-- If w ∈ [a , b) and we know t ∈ C w and ¬ C i for all i ∈ (a , b)
-- then it must be that w ≡ a.
firstOfIval
    : {w a b : ℕ}
    → a ≤ w
    → w < b
    → (P : ℕ → Set)
    → ((ℓ : ℕ) → Between a b ℓ → ¬ P ℓ)
    → P w
    → w ≡ a
firstOfIval {w} {a} {b} a≤w w<b P H Pw = ?
