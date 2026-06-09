-- Module      : Eser.Filters
-- Description : Sketch of the 'filter'-version of localisible predicates.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------

open import Data.Nat
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.Sum
open import Function using (_∘_ ; _$_)

open import Eser.EqRel.Definitions using (NFFun)
open import Eser.Aux using (_↔_)
module Eser.Filters where

--------------------------------------------------------------------------------
-- # Big-picture summary
--
-- This story is about an inductive way of constructing certain predicates
-- on decidable equivalence relations on enumerable types.
--
-- The idea is as follows.
-- Let A = {a₀, a₁, a₂, a₃, ...} ≃ ℕ be the enumerable type.
-- Identify equivalence relations with normalisation functions:
-- f : ℕ → ℕ
-- f (f n) ≡ f n
-- f n ≤ n
-- So an equivalence relation is an assignment of normal forms to terms of A.
-- For every prefix of A, denoted Aₙ = {a₀, a₁, ..., aₙ₋₁},
-- corresponding to {0, 1, ..., n-1} under the A ≃ ℕ equivalence.
-- We can build an equivalence relation by inductively extending, for all n : ℕ,
-- a partial equivalence relation fₙ : Fin n → Fin n
-- by choosing the normal form of n, extending the function 
-- to Fin (1+n) → Fin(i+n). We start with the empty relation at n = 0.
--
-- Which choices are available?
-- * One existing normal of fₙ, i.e., a number in the image of fₙ.
-- * Make n a new normal form, i.e., the least element of a new equivalence
-- class.
--
-- ## Filters
--
-- Now, a 𝐅𝐈𝐋𝐓𝐄𝐑 restricts those choices.
-- Consequently, this restricts the possible equivalence relations one can
-- construct.
-- We say that a normalisation function f satisfies a filter F, if 
-- all fₙ₌₁ extend fₙ with a choice that F(fₙ) allows.
-- Thus, every filter gives rise to a predicate on equivalence relations.
--
-- We implement filters as functions mapping restricted normalisation functions
-- (fₙ can be encoded as a vector of numbers of length n) to Bool.
-- This allows to easily compose filters by pointwise taking their ∧.
-- 
-- If one can prove that there is a series of choices such that all are allowed
-- by a filter, then one can extract a normalisation function from the filter;
-- for example, by picking the maximum allow choice at every point.
-- This normalisation function f then, by construction,
-- satisfies the filter, and also f (f n) ≡ f n and f n ≤ n.
--
-- The latter two conditions could also have been implemented as filters,
-- but instead we build those two conditions in our representation of
-- restrictions such that they hold by construction -- we are not interested in
-- functions that are not normalisation functions anyway.
--
-- ## Restriction Coherent families of predicates
--
-- Another concept we introduce are "Restriction Choherent families of
-- predicates", or just '𝐑𝐞𝕔𝕠's for short.
-- They are families P of predicates on restrictions of nf functions,
-- such that if P (f₁₊ₙ) ≡ true then also P (fₙ) ≡ true.
-- They are in a bijective correspondence with filters,
-- up to extensionality: for every predicate implementable as a filter
-- there exists a reco that also implements it, and vice versa.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- Representation of restrictions of normalisation functions
--------------------------------------------------------------------------------
-- We could have used functions `Fin n → Bool` or `Vec ℕ n`,
-- but then the conditions `f (f n) ≡ f n` and `f n ≤ n`
-- must either be omitted or given externally.
-- More convenient is to use correct-by-construction vectors.
-- They are a bit like fresh lists, but instead of a freshness condition
-- on appendable elements
-- we have a constraint set of choices of appendable elements.
-- This set of choices depends on the *entire* existing list,
-- unlike in fresh lists where the appendum needs to be < than all elements in
-- the list.
--
-- There are three constructors:
-- 1. empty: the canonical normalisation function on ∅.
-- 2. newNF: extend a nf function on {0, 1, ..., n-1} 
--  to {0, 1, ..., n} by making n a new normal form.
-- 3. oldNF: extend a nf function f on {0, 1, ..., n-1} 
--  to {0, 1, ..., n} by normalising n to an existing normal form of f.
--
-- Note that oldNF requires the type of normal-forms of f.
-- We define those via mutual induction.
-- It has three constructors:
-- 1. here: if the last element of a NFRestr is a normal form, 
--  then pick that one.
-- 2. earlier-new: pick a normal form (not the last one!) of a NFRestr
--  whose last element is a normal form.
-- 3. earlier-old: pick a normal form of a NFRestr
--  whose last element is NOT a normal form.
--
-- NOTE: earlier-old takes two normal forms as input.
-- Don't confure them: the first is the normal form of the last element of the
-- NFRestr, which we need just to express the index in the type. 
-- The second is the normal form that the constructor tries to describe.

data NFRestr : ℕ → Set 
data NFS : {n : ℕ} → NFRestr n → Set

data NFRestr where
    empty : NFRestr 0
    newNF 
        : {n : ℕ} 
        → NFRestr n 
        → NFRestr (ℕ.suc n)
    oldNF 
        : {n : ℕ}
        → (r : NFRestr n)   --^ Function to extend.
        → NFS r             --^ Existing normal form.
        → NFRestr (ℕ.suc n)
    
data NFS where
    here 
        : {n : ℕ} 
        → {r : NFRestr n} 
        → NFS (newNF r)
    earlier-new
        : {n : ℕ} 
        → {r : NFRestr n} 
        → NFS r
        → NFS (newNF r)
    earlier-old
        : {n : ℕ} 
        → {r : NFRestr n} 
        → {c : NFS r}       --^ Normal form of last element of r.
        → NFS r             --^ Normal form that we are now describing.
        → NFS (oldNF r c)

-- When extending a `r : NFRestr n` with the next element n, 
-- one can choose the normal form of the new element to be n itself.
-- This normal form does not yet exist in r, but it does in `newNF r`.
Choices : {n : ℕ} → NFRestr n → Set
Choices r = NFS (newNF r)

addChoice : {n : ℕ} → (r : NFRestr n) → Choices r → NFRestr (ℕ.suc n)
addChoice r here = newNF r
addChoice r (earlier-new c) = oldNF r c
-- Note: the case `earlier-old c` is impossible because it is not
-- a normal form in `Choices r ≗ NFS (newNF r)`.

-- Restrict a normalisation function into a NFRestr
restrict : NFFun → (n : ℕ) → NFRestr n
restrict (f , f-leq , f-fix) n = ?

-- Important is to show that for every NFRestr there actually is a normalisation
-- function whose restriction is represents.
theo-all-nFRestr-reachable
    : {n : ℕ}
    → (r : NFRestr n)
    → Σ[ f ∈  NFFun ](r ≡ restrict f n)
theo-all-nFRestr-reachable {n} r = ?

--------------------------------------------------------------------------------
-- Filters
--------------------------------------------------------------------------------
Filter : Set
Filter = {n : ℕ} → (r : NFRestr n) → Choices r → Bool

--------------------------------------------------------------------------------
-- Restriction Coherent families of predicates (recos)
--------------------------------------------------------------------------------
-- Encoded as a record.
-- Fields:
-- * pred: the actual family of predicates.
-- * coherence: if an extension of an r : NFRestr n satisfies the predicates,
--  then so must r be itself.
-- * empty-is-ok: the empty NFRestr must always be satisfied.
--  This is a technical detail to make the correspondence with Filters work,
--  since a Filter cannot encode any judgement about the empty relation
--  (because, you know, there was no choice made in order to construct it,
--  so also no set of choices to constrain).

-- Relation r ⋖ s expressing that s extends r with exactly one more choice.
infixl 4 _⋖_ -- `lessdot` is the Cornelis shortcut for `⋖`.
data _⋖_ : {n : ℕ} → (r : NFRestr n) → (s : NFRestr (ℕ.suc n)) → Set where
    ⋖-newNF : {n : ℕ} → (r : NFRestr n) → r ⋖ (newNF r)
    ⋖-oldNF : {n : ℕ} → (r : NFRestr n) → (c : NFS r) →  r ⋖ (oldNF r c)

record Reco : Set where
    constructor reco
    field
        predicate
            : {n : ℕ}
            → NFRestr n
            → Bool
        coherence
            : {n : ℕ}
            → (r : NFRestr n)
            → (s : NFRestr (ℕ.suc n))
            → r ⋖ s
            → predicate s ≡ true
            → predicate r ≡ true
        empty-is-ok
            : predicate empty ≡ true

--------------------------------------------------------------------------------
-- Correspondence Filters and Recos
--------------------------------------------------------------------------------
filterToReco : Filter → Reco
filterToReco = ?

infixl 4 filterToReco
syntax filterToReco F = ↑ F

recoToFilter : Reco → Filter
recoToFilter = ?

infixl 4 recoToFilter
syntax recoToFilter P = ↓ P

Filter-sats : Filter → NFFun → Set
Filter-sats = ?

Reco-sats : Reco → NFFun → Set
Reco-sats = ?

theo-filter-reco-correspondence
    : (F : Filter)
    → (f : NFFun)
    → Filter-sats F f ↔ Filter-sats (↓ ↑ F) f
theo-filter-reco-correspondence F f = ?
    
theo-reco-filter-correspondence
    : (P : Reco)
    → (f : NFFun)
    → Reco-sats P f ↔ Reco-sats (↑ ↓ P) f
theo-reco-filter-correspondence P f = ?

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

infixl 4 _♥_
_♥_ : (F G : Filter) → Set
_♥_ F G = 
    {n : ℕ}
    → (r : NFRestr n)
    → (AllRestr-sat (F ⋀ G) r)
    → Σ[ c ∈ Choices r ] (F ⋀ G) r c ≡ true

--------------------------------------------------------------------------------
-- TODOs
--------------------------------------------------------------------------------
-- * Sheets `⋄`: PointwiseChooser and aux lemmas.

