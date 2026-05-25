-- Module      : Eser.ListSubstExp
-- Description : Experiment about nature of `subst`
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- Question: given a list of elements x : Σ[ n ∈ ℕ ](B n)
-- together with proofs hₓ : proj₁ x ≡ mₓ.
-- Can we then get a list of elements of types (B mₓ)?
--
-- Motativation: decomposeTerm needs to use `subst` to turn a list
-- of pairs (x , hₓ) into elements of types (B mₓ).
-- But `subst hₓ B (proj₂ x) : B mₓ` is not judgementally equal to `proj₁ x`.
-- Yet decomposeTerm should be an inverse, so we somehow need to go back to
-- `proj₁ x`.
--
-- Outcome: success!
-- This gives me sufficient hope that it will be provable that decomposeTerm is
-- has an inverse. Of course, within decomposeTerm things may be a bit more
-- complicated than in this isolated setting.

open import Data.Nat
open import Data.Sum hiding (map)
open import Data.Unit
open import Data.Product hiding (map)
open import Data.List
open import Relation.Binary.PropositionalEquality


module Eser.ListSubstExp where

MyType : (ℕ → Set) → Set
MyType B = Σ[ n ∈ ℕ ] (B n)

substAll : 
    {B : ℕ → Set}
    (L : List (Σ[ x ∈ MyType B ](Σ[ mₓ ∈ ℕ ](proj₁ x ≡ mₓ))))
    → List (MyType B)
substAll {B} [] = []
substAll {B} ((x , mₓ , hₓ) ∷ xs) = (mₓ , subst B hₓ (proj₂ x)) ∷ (substAll xs)


substAllTheorem : 
    {B : ℕ → Set}
    (L : List (Σ[ x ∈ MyType B ](Σ[ mₓ ∈ ℕ ](proj₁ x ≡ mₓ))))
    → substAll L ≡ map proj₁ L
substAllTheorem {B} [] = refl
substAllTheorem {B} ((x , mₓ , refl) ∷ xs) = 
    let restEq : substAll xs ≡ map proj₁ xs
        restEq = substAllTheorem xs
    in
    -- The first term in substAll ((x , mₓ , refl) ∷ xs),
    -- defined as (mₓ , subst B hₓ (proj₂ x)), normalises
    -- to x, since refl proves that proj₁ x is mₓ,
    -- and the subst with input hₓ ≐ refl normalises
    -- to proj₂ x, and x ≐ (proj₁ x , proj₂ x)
    -- is a standard computation rule of Σ-types in type theory.
    cong (λ L' → x ∷ L') restEq
