-- Module      : Eser.Filters.Base
-- Description : Base definitions of filters and normalisation function restr.
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
open import Data.Maybe

open import Data.Nat.Properties using (≤-refl ; ≤-trans ; n≤1+n)

open import Eser.EqRel.Definitions using (NFFun ; DecEquiv)
open import Eser.EqRel.Conversions using (RelToFun)
open import Eser.Aux using (_↔_ ; _≈_)

module Eser.Filters.Base where

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

Predicate : Set₁
Predicate = DecEquiv → Set

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


-- Relation r ⋖ s expressing that s extends r with exactly one more choice.
infixl 4 _⋖_ -- `lessdot` is the Cornelis shortcut for `⋖`.
data _⋖_ : {n : ℕ} → (r : NFRestr n) → (s : NFRestr (ℕ.suc n)) → Set where
    ⋖-newNF : {n : ℕ} → (r : NFRestr n) → r ⋖ (newNF r)
    ⋖-oldNF : {n : ℕ} → (r : NFRestr n) → (c : NFS r) →  r ⋖ (oldNF r c)

-- Derived constructor that works for both kinds of choices.
⋖-addChoice : {n : ℕ} → {r : NFRestr n} → (c : Choices r) → r ⋖ addChoice r c
⋖-addChoice {n} {r} here = ⋖-newNF r
⋖-addChoice {n} {r} (earlier-new c) = ⋖-oldNF r c

-- (Σ[ c ∈ Choices r ] s ≡ addChoice r c) and (r ⋖ s) are essentially
-- the same statement. ⋖-addChoice gives the conversion in one direction,
-- here is the reverse conversion:
⋖-to-addChoice
    : {n : ℕ} 
    → {r : NFRestr n} 
    → {s : NFRestr (ℕ.suc n)} 
    → r ⋖ s
    → Σ[ c ∈ Choices r ] s ≡ addChoice r c
⋖-to-addChoice {n} {r} {newNF r} (⋖-newNF r) = (here , refl)
⋖-to-addChoice {n} {r} {oldNF r c} (⋖-oldNF r c) = (earlier-new c , refl)

-- Transitive closure of above relation.
-- Note: the implementation could have used
-- `⋖+-multistep : r ⋖+ s → s ⋖ t → r ⋖+ t` instead
-- of the 2 multistep constructors we have now,
-- but in practise one would pattern match on `s ⋖ t` and obtain the same two
-- cases anyway.
data _⋖+_ : {n m : ℕ} → (r : NFRestr n) → (s : NFRestr m) → Set where
    ⋖+-onestep 
        : {n : ℕ} 
        → {r : NFRestr n} 
        → {s : NFRestr (ℕ.suc n)} 
        → r ⋖ s
        → r ⋖+ s
    
    ⋖+-multistep-newNF
        : {n m : ℕ} 
        → {r : NFRestr n} 
        → {s : NFRestr m}
        → r ⋖+ s
        → r ⋖+ (newNF s)

    ⋖+-multistep-oldNF
        : {n m : ℕ} 
        → {r : NFRestr n} 
        → {s : NFRestr m}
        → (c : NFS s)
        → r ⋖+ s
        → r ⋖+ (oldNF s c)

-- Derived constructor (works for both ways of proving s' ⋖ s):
⋖+-multistep-anychoice
    : {n m : ℕ} 
    → {r : NFRestr n} 
    → {s' : NFRestr m}
    → {s : NFRestr (suc m)}
    → r ⋖+ s'
    → s' ⋖ s
    → r ⋖+ s
⋖+-multistep-anychoice {n} {m} {r} {s'} {s} r⋖+s' (⋖-newNF s') = 
    ⋖+-multistep-newNF r⋖+s'
⋖+-multistep-anychoice {n} {m} {r} {s'} {s} r⋖+s' (⋖-oldNF s' c) =
    ⋖+-multistep-oldNF c r⋖+s'

-- Transitive & reflexive closure
_⋖+=_ : {n m : ℕ} → (r : NFRestr n) → (s : NFRestr m) → Set
_⋖+=_ {n} {m} r s = (Σ[ p ∈ m ≡ n ] (r ≡ subst NFRestr p s)) ⊎ (r ⋖+ s)

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
-- Extension sequences
--------------------------------------------------------------------------------
-- Normalisation functions are roughly the same as a 
-- a sequence of NFRestrs that extend each other with an additional
-- choice.
-- Exence - short for "EXtensions sequENCE" - is easier for the tongue
-- and mind than "CoherentNFRestrFam".
--
-- We can combine such a sequence into an NFFun,
-- and restrict a Exence into 
-- which is (up to function extensionality) the inverse of `restrict`.
-- See Eser.Filters.Conversions.NFFunToExence for the conversions.

NFRestrFam : Set
NFRestrFam = (n : ℕ) → NFRestr n
Exence : Set
Exence = Σ[ h ∈ NFRestrFam ]((n : ℕ) → h n ⋖ h (ℕ.suc n))
--------------------------------------------------------------------------------
-- TODOs
--------------------------------------------------------------------------------
-- * Sheets '◊': PointwiseChooser and aux lemmas.
-- * add lemma that extract-maxchoice-nf is pointwise actually the maximum
-- choice.


--------------------------------------------------------------------------------
-- Functions on NFRestrs.
--------------------------------------------------------------------------------

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
-- Case 1: the input NFRestr chose the normal form of n to be itself.
NFSToℕ {suc n} {newNF r} here = n 
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
choiceToℕ {n} {r} c = NFSToℕ {ℕ.suc n} {newNF r} c 

NFSToℕ-< 
    : {n : ℕ}
    → {r : NFRestr n}
    → (x : NFS r)
    → NFSToℕ x < n
NFSToℕ-< {suc n} {newNF r} here = s≤s ≤-refl
NFSToℕ-< {suc n} {newNF r} (earlier-new x) = s≤s (≤-trans (n≤1+n (NFSToℕ x)) y)
    where 
        y : NFSToℕ x < n
        y = NFSToℕ-< {n} {r} x
NFSToℕ-< {suc n} {oldNF r c} (earlier-old x) = s≤s (≤-trans (n≤1+n (NFSToℕ x)) y)
    where 
        y : NFSToℕ x < n
        y = NFSToℕ-< {n} {r} x

-- Get the normal form of the last chosen element as a number in ℕ.
-- Note that the last choice in a NFRestr n chose a normal form for n-1;
-- so in particular, a NFRestr 0 does not record any choice,
-- so no output can be defined (hence the `Maybe`).
NFRestrToℕ : {n : ℕ} → NFRestr n → Maybe ℕ
NFRestrToℕ {n} empty = nothing
NFRestrToℕ {suc n'} (newNF r') = just n'
NFRestrToℕ {suc n'} (oldNF r' c) = just $ NFSToℕ {n'} {r'} c
