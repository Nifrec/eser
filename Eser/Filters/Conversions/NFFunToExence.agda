-- Module      : Eser.Filters.Conversions.NFFunToExence
-- Description : Converting a NFFun to extensions-sequence, and inversity proof.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.Sum
open import Function using (_∘_ ; _$_)

open import Eser.EqRel.Definitions using (NFFun ; DecEquiv)
open import Eser.EqRel.Conversions using (RelToFun)
open import Eser.Aux using (_↔_ ; _≈_)

open import Eser.Filters.Base

module Eser.Filters.Conversions.NFFunToExence where

-- Restrict a normalisation function into an Exence --
-- a sequence of NFRestrs that extend each other.
restrict+ : NFFun → Exence
restrict+ f = (? , ?)

-- Restrict a normalisation function into a NFRestr
restrict : NFFun → (n : ℕ) → NFRestr n
restrict = proj₁ ∘ restrict+

-- Given r ⋖ s, extract the choice that extends r into s.
getChoice 
    : {n : ℕ}
    → (r : NFRestr n)
    → (s : NFRestr (ℕ.suc n))
    → r ⋖ s
    → Choices r
getChoice r (newNF r) (⋖-newNF r) = here
getChoice r (oldNF r c) (⋖-oldNF r c) = earlier-new c

-- Given a sequence of extensions, extract the choice that
-- extends h n to h (1+n).
getChoiceFromExence : (hH : Exence) → (n : ℕ) → Choices ((proj₁ hH) n)
getChoiceFromExence (h , H) n = getChoice (h n) (h $ ℕ.suc n) (H n)

NFSToℕ 
    : {n : ℕ}
    → {r : NFRestr n}
    → NFS r
    → ℕ
-- Case 1: r chose the normal form of n to be itself.
NFSToℕ {suc n} {r} here = n 
-- Case 2 & 3: the input normal form is a normal form of a sub-restriction
-- of r. So recurse on this sub-restriction.
NFSToℕ {suc n} {newNF r} (earlier-new x) = NFSToℕ {n} {r} x
NFSToℕ {suc n} {oldNF r c} (earlier-old x) = NFSToℕ {n} {r} x

choiceToℕ 
    : {n : ℕ}
    → {r : NFRestr n}
    → Choices r
    → ℕ
-- A choice of r is a NF of newNF r, by definition of `Choices`.
choiceToℕ {n} {r} c = NFSToℕ c 

NFSToℕ-≤ 
    : {n : ℕ}
    → {r : NFRestr n}
    → (x : NFS r)
    → NFSToℕ x < n
NFSToℕ-≤ = ?

NFSToℕ-<
    : {n : ℕ}
    → {r : NFRestr (ℕ.suc n)}
    → (x : NFS r)
    → NFSToℕ x ≤ n
NFSToℕ-< = s≤s⁻¹ ∘ NFSToℕ-≤

combine : Exence → NFFun
combine (h , H) = (f , f-leq , f-fix)
    where
        
        f : ℕ → ℕ
        f = choiceToℕ ∘ (getChoiceFromExence (h , H))

        f-leq : (n : ℕ) → f n ≤ n
        f-leq n = ?

        f-fix : (n : ℕ) → f (f n) ≡ f n
        f-fix n = ?


--------------------------------------------------------------------------------
-- Properties of the conversions
--------------------------------------------------------------------------------
-- 1. Every NFRestr is actually 'reachable', i.e., actually a restriction
--  of some NFFun.
-- 2. combine & restrict+ form a pair of inverses
--  (up to function extensionality and first projections).

-- Important is to show that for every NFRestr there actually is a normalisation
-- function whose restriction is represents.
theo-all-NFRestr-reachable
    : {n : ℕ}
    → (r : NFRestr n)
    → Σ[ f ∈  NFFun ](r ≡ restrict f n)
theo-all-NFRestr-reachable {n} r = ?

theo-restrict-combine
    : (f : NFFun)
    →  (proj₁ ∘ combine ∘ restrict+) f ≈ proj₁ f
theo-restrict-combine f = ?

theo-combine-restrict
    : (H : Exence)
    → (proj₁ ∘ restrict+ ∘ combine) H ≈ proj₁ H
theo-combine-restrict H = ?
