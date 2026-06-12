-- Module      : Eser.Filters.PointwiseProperties
-- Description : Pointwise defined properties of Filters and NFRestrFams.
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
open import Eser.Filters.Conversions.NFFunToExence

module Eser.Filters.PointwiseProperties where

--------------------------------------------------------------------------------
-- Predicates whether an NFFun satisfies a Filter/Reco
--------------------------------------------------------------------------------

Filter-sats : Filter → NFFun → Set
Filter-sats = ?


Reco-sats : Reco → NFFun → Set
Reco-sats = ?

--------------------------------------------------------------------------------
-- Filter compatibility relation
--------------------------------------------------------------------------------
-- F ♥ G if there exists a sequence of normalisation function extensions
-- whose choices both F and G allow, i.e., F ♥ G iff there exisits
-- a normalisation function that satisfies both.
--
-- ## Remark 1
-- _♥_ is symmetric, but not reflexive and not transitive.
-- F ♥ F is a nontrivial statement that there exists a normalisation
-- function satisfying F.
--
-- ## Remark 2
-- The following definition is wrong:
--      (F ♥ G) r = Σ[ c ∈ Choices r ] F r c ∧ G r c
-- This condition is too strong, because it requires F and G
-- to agree on some extension of any NFRestr r, even
-- NFRestr r containing earlier choices which neither F nor G accepts.
-- That is not needed to encode the intended 'there exists a normalisation
-- function F and G both accept'.

infixl 4 _⋀_ -- `And` in Cornelis. `and` (for `∧`) is on Bool.
_⋀_ : Filter → Filter → Filter
(F ⋀ G) {n} r c = F r c ∧ G r c

-- All sub-restrictions of a restriction satisfy a filer.
data AllRestr-sat (F : Filter) : {n : ℕ} → NFRestr n → Set where
    allsat-empty : AllRestr-sat F empty
    allsat-newNF 
        : {n : ℕ} 
        → (r : NFRestr n) 
        → AllRestr-sat F r
        → (F r here ≡ true)
        → AllRestr-sat F (newNF r)
    allsat-oldNF 
        : {n : ℕ} 
        → (r : NFRestr n) 
        → (c : NFS r)
        → AllRestr-sat F r
        → (F r (earlier-new c) ≡ true)
        → AllRestr-sat F (oldNF r c)

-- A filter is passable if there exists a sequence of choices
-- that the filter accepts at every point.
Passable : Filter → Set
Passable F = 
    {n : ℕ}
    → (r : NFRestr n)
    → (AllRestr-sat F r)
    → Σ[ c ∈ Choices r ] F r c ≡ true

infixl 4 _♥_
_♥_ : (F G : Filter) → Set
_♥_ F G = Passable (F ⋀ G)

-- #TODO: use idempotence of ⋀
self-compat-to-passable
    : {F : Filter}
    → F ♥ F
    → Passable F
self-compat-to-passable = ?

--------------------------------------------------------------------------------
-- Extracting a normalisation function out of a satisfiable filter
--------------------------------------------------------------------------------
-- If F ♥ F, then there exists at least one normalisation function
-- satisfying F. There may be multiple. 
-- Two obvious such functions are as follows:
-- * Always choose the smallest allowed choice.
--      (This minimises the number of equivalence classes).
-- * Always choose the largest allowed choice.
--      (This maximises the number of equivalence classes).
-- For many actual filters I consider to implement, the first one becomes
-- trivial: it always can choose 0, and does so accordingly;
-- resulting in one boring equivalence class.
-- However, choosing the largest often gives the desired relation.

--#TODO: remove and update documentation above.
extract-maxchoice-nf
    : {F : Filter}
    → F ♥ F
    → Σ[ f ∈ NFFun ] (Filter-sats F f)
extract-maxchoice-nf {F} F♥F = ?

-- An NFFun maximises the number of equivalence classes if it introduces
-- a new normal form whenever allowed by F.
-- This property is probably only useful if `Filter-sats F f`,
-- but can be defined without assuming that.
MaximisesClasses : Filter → NFFun → Set
MaximisesClasses F f = {!
    (n : ℕ)
    → (F (restrict f n) here ≡ true)
    → getChoice f n ≡ here !}

-- Extract a normalisation function from a passable
extract-maxclass-nf
    : {F : Filter}
    → Passable F
    → Σ[ f ∈ NFFun ] (Filter-sats F f ) × (MaximisesClasses F f)
extract-maxclass-nf {F} pass = (f' , f-stats-F , f-max-classes)
    where
        f : ℕ → ℕ
        f = ?

        f-leq : (n : ℕ) → f n ≤ n
        f-leq n = ?

        f-fix : (n : ℕ) → f (f n) ≡ f n
        f-fix n = ?

        f' : NFFun
        f' = (f , f-leq , f-fix)

        f-stats-F : (Filter-sats F f' )
        f-stats-F = ?

        f-max-classes : (MaximisesClasses F f')
        f-max-classes = ?




