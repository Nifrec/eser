-- Module      : Eser.ListMaxima
-- Description : Auxiliary lemmas about maximas of lists of natural numbers.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- Note: max n L in the standard library is defined via folding.
-- So it returns n if all elements of L are smaller/equal than n,
-- and in particular, also if L is empty.

open import Data.Nat
open import Data.Nat.Properties using (<-≤-trans ; n≢0⇒n>0 )
open import Data.List
open import Data.List.Extrema.Nat
open import Data.List.Membership.Propositional using (_∈_)
open import Data.List.Relation.Unary.All renaming (lookup to All-lookup)
open import Relation.Binary.PropositionalEquality
open import Data.Sum
open import Function
open import Relation.Nullary
open import Data.List.Relation.Unary.Any 
open import Data.Empty

module Eser.ListMaxima where

maxIsDefaultOrIn
    : (L : List ℕ)
    → max 0 L ≡ 0 ⊎ max 0 L ∈ L
maxIsDefaultOrIn = argmax-sel id 0

nonemptyThenHasMax
    : { L : List ℕ}
    → 0 < length L
    → max 0 L ∈ L
nonemptyThenHasMax {[]} ()
nonemptyThenHasMax {L@(x ∷ L')} _ with maxIsDefaultOrIn L
... | inj₂ max0L∈L = max0L∈L
... | inj₁ max0L≡0 with x Data.Nat.≟ 0
...     | yes x≡0 = 
                let x∈L : x ∈ L
                    x∈L = Any.here refl
                in
                subst (λ v → v ∈ L) (trans x≡0 (sym max0L≡0)) x∈L
...     | no x≢0 = 
                let x∈L : x ∈ L
                    x∈L = Any.here refl
                in
                let x≤max : x ≤ max 0 L
                    -- Need to eliminate an ``All`` predicate here.
                    x≤max = All-lookup (xs≤max 0 L) x∈L
                in
                let 0<x : 0 < x
                    0<x = n≢0⇒n>0 x≢0
                in
                let max<x : max 0 L < x
                    max<x = subst (λ y → y < x) (sym max0L≡0) 0<x
                in
                let max<max : max 0 L < max 0 L
                    max<max = <-≤-trans max<x x≤max
                in
                ⊥-elim (Data.Nat.Properties.<-irrefl refl max<max)
    
