-- Module      : Eser.Signature.JumpEnum
-- Description : Equivalence between sums-of-fin-sets to natural numbers.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- The type Σ[ x ∈ ℕ ] Fin (f x) is equivalent to ℕ if infinitely
-- many `Fin (f x)`s are inhabited.
-- Having a function that maps from an inhabited x ∈ ℕ
-- to the next inhabited x' ∈ ℕ (so f(x) ≥ 1, f(x') ≥ 1, x' > x)
-- (and skipping over all intermediate x'' with f(x'') = 0)
-- is sufficient to establish the equivalence.

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
open import Eser.Equivalences.Notation
open import Eser.Equivalences.Properties
open import Eser.Aux
open import Eser.Signature.Definitions

module Eser.Signature.JumpEnum where

-- `iter f n a` returns fⁿ(a), i.e., f applied n times starting from a.
iter : {A : Set} → (A → A) → ℕ → A → A
iter {A} f 0 a = a
iter {A} f (suc n) a = f (iter f n a)

--------------------------------------------------------------------------------
-- Skip-over-⊥s theorem
-- A sum over a family of types is equivalent to the sum
-- over the same types except with the empty ones left out.
--
-- One could prove a more general statement than presented here,
-- but this version is most convenient for our use case.
--------------------------------------------------------------------------------

-- A function that jumps from one to the next inhabited type
-- given an ℕ-indexed family of types.
InhabitJumper : (C : ℕ → Set)  → Set
InhabitJumper C 
    = {w : ℕ} 
    → C w
    → Σ[ h ∈ ℕ ] (
       --^ Jumping distance (minus one).
       (C $ w + 1 + h) 
       --^ The destination is inhabited, ...
       × 
       ((x : ℕ) → (w < x × x < w + 1 + h) → ¬ C x) 
       --^ ... but intermediate points are not.
    )
-- Note: the argument `C w` might seem redundant.
-- For my use case it could indeed be avoided,
-- but the implementation of an actual jumper simplifies a lot if we can
-- depart from the latest inhabited point.
-- The alternative is to take multiple jumps from the first inhabited points,
-- until one reaches the first point beyond w; this is more work to prove right
-- in Agda.

-- Iterate an InhabitJumper from an inhabited starting point n₀,
-- and give the point reached after n jumps.
-- (In out use case (see below), we'll have ¬ C 0 but C 1 is inhabited, 
-- so we start with n₀ ≔ 1).
J-iter : {C : ℕ → Set} → (n₀ : ℕ) → C n₀ → (J : InhabitJumper C) → ℕ → ℕ
J-iter {C} n₀ t₀ J 0 = n₀
--J-iter {C} n₀ t₀ J (suc n) = proj₁ $ depGIter g J' n (n₀ , t₀)
J-iter {C} n₀ t₀ J (suc n) = proj₁ $ iter J' n (n₀ , t₀)
    where
        J' : Σ[ w ∈ ℕ ] C w → Σ[ w ∈ ℕ ] C w
        J' (w , t) = 
            let (h , t' , _) = J {w} t
            in
            (w + 1 + h , t')

jumpOver⊥s
    : (C : ℕ → Set)
    → (J : InhabitJumper C)
    → (¬ C 0)
    → (t₀ : C 1)
    → (Σ[ w ∈ ℕ ] C w) ≃ (Σ[ n ∈ ℕ ] (C $ J-iter 1 t₀ J n))
jumpOver⊥s _ _ _ _ = ? -- See sheet "Lih 11" backside

jumpTheoremInhabitJumper
    : {C : ℕ → Set}
    -- ^ Type of 'pitstops' the jumping function can visit.
    → (a₀ : C 1)
    -- ^ Proof the starting pitstop with index 1 is inhabited.
    → (J : InhabitJumper C)
    -- ^ Function to jump between pitstops.
    → ((w : ℕ) → Σ[ z ∈ ℕ ]( C w ≃ Fin z ))
    -- ^ Every point (incl. non-pitstops) is some finite set.
    → ((i : ℕ) → Σ[ z' ∈ ℕ ] (C (J-iter {C} 1 a₀ J i) ≃ Fin (ℕ.suc z')))
    -- ^ But when only looking at pitstops, they are inhabited finite sets.
jumpTheoremInhabitJumper = ? -- Sheet "Lih 10".
