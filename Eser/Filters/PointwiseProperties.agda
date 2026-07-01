-- Module      : Eser.Filters.PointwiseProperties
-- Description : Pointwise defined properties of Filters and NFRestrFams.
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

open import Eser.EqRel.Definitions using (NFFun ; DecEquiv)
open import Eser.EqRel.Conversions using (RelToFun)
open import Eser.Aux using (_↔_ ; _≈_)

open import Eser.Filters.Base
open import Eser.Filters.Conversions.NFFunToExence

module Eser.Filters.PointwiseProperties where

--------------------------------------------------------------------------------
-- Predicates whether an NFFun satisfies a Filter/Reco
--------------------------------------------------------------------------------

Exence-sats : Filter → Exence → Set
Exence-sats F (h , H) = (n : ℕ) → F (h n) (getChoiceFromExence (h , H) n) ≡ true

NFFun-sats : Filter → NFFun → Set
NFFun-sats F f' = Exence-sats F (restrict+ f')

Reco-sats : Reco → NFFun → Set
Reco-sats = ?

-- All sub-restrictions of a restriction satisfy a filter.
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

--------------------------------------------------------------------------------
-- Satisfiable Filters
--------------------------------------------------------------------------------
-- A Filter is satisfiable that allow a complete sequence of choices
-- of normal forms for each n : ℕ.
--
-- We define a Filter to be 'Passable' if such a sequence exists.
--
-- The most interesting Filters are those that allow to locally "grow" a
-- normalisation function, by choosing recursively extensions
-- that satisfy the Filter. 
-- The Filter ought then to be nice and allow the growth to continue,
-- meaning some choice of extension is available if all previous choices
-- are allowed by the Filter. 'Passability' is not a sufficient strong
-- condition: it gives a series of default choices, but divering from those
-- defaults may still get the growth to get stuck in a partial normalisation
-- function with no allowed extension.
-- So we define the stronger notion of "DeadEndFree".

-- A filter is passable if there exists a sequence of choices
-- that the filter accepts at every point.
Passable : Filter → Set
Passable F = Σ[ E ∈ Exence ] Exence-sats F E

-- A filter is DeadEndFree if for any sequence of allowed choices
-- there always extists an allowed extension.
-- Diverging from those 'default' allowed extensions and choosing
-- other allowed extensions will never lead to an NFRestr 
-- without allowed further extensions.
DeadEndFree : Filter → Set
DeadEndFree F = 
    {n : ℕ} 
    → (r : NFRestr n) 
    → AllRestr-sat F r 
    → Σ[ c ∈ Choices r ] F Allows c In r

lemma-DEF-to-Passable
    : (F : Filter)
    → DeadEndFree F
    → Passable F
lemma-DEF-to-Passable F = ?

--------------------------------------------------------------------------------
-- Filter compatibility relation
--------------------------------------------------------------------------------
-- F ♥ G if for every sequence of normalisation function extensions
-- whose choices both F and G allow there exist an extension they also both
-- allow, i.e., F ♥ G is DeadEndFree.
--
-- ## Remark 1
-- _♥_ is symmetric, but not reflexive and not transitive.
-- F ♥ F is a nontrivial statement that F is DeadEndFree.
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

infixl 4 _♥_
_♥_ : (F G : Filter) → Set
_♥_ F G = DeadEndFree (F ⋀ G)

-- #TODO: use idempotence of ⋀
self-compat-to-passable
    : {F : Filter}
    → F ♥ F
    → DeadEndFree F
self-compat-to-passable = ?

--------------------------------------------------------------------------------
-- Extracting a normalisation function out of a satisfiable filter
--------------------------------------------------------------------------------
-- If F ♥ F, then there exists at least one normalisation function
-- satisfying F. There may be multiple. 
-- Some of such functions are as follows:
-- 1. Always pick the witnessing-choice given by the proof of F ♥ F.
-- 2. Introduce a new equivalence class when possible, otherwise
--      use the witnessing-choice of F ♥ F 
--      (implemented below as `extract-maxclass-nf).
--      (This maximises the number of equivalence classes).
-- 3. Always choose the largest allowed choice.
--      (This maximises the number of equivalence classes).
-- 4. Always choose the smallest allowed choice.
--      (This minimises the number of equivalence classes).
-- For many actual filters I consider to implement, the last one becomes
-- trivial: it always can choose 0, and does so accordingly;
-- resulting in an equivalence relation of just one boring equivalence class.
-- However, options 2 and 3 often give the desired relation.

-- Predicate that an Exence chooses to introduce a new equivalence class
-- whenever the filter allows it.
-- For many filters this is the same as maximising the number of equivalence
-- classes, although some filters may allow more equivalence classes
-- to be introduced later when fewer introduced earlier.
-- Hence "Greedily". 
GreedilyIntroducesClasses : Filter → Exence → Set
GreedilyIntroducesClasses F (h , H) = 
    (n : ℕ) 
    → F (h n) (here {n} {h n}) ≡ true 
    → getChoiceFromExence (h , H) n ≡ here {n} {h n}

extract-greedynewclass-exence
    : {F : Filter}
    → DeadEndFree F
    → Σ[ H' ∈ Exence ] (Exence-sats F H' ) × (GreedilyIntroducesClasses F H')
extract-greedynewclass-exence {F} pass = ((h , H) , hH-sats-F , hH-greedy)
    where
        -- z and h are defined in mutual induction.

        h : (n : ℕ) → NFRestr n
        z : (n : ℕ) → AllRestr-sat F (h n)

        h = ?
        z = ?
        H : (n : ℕ) → h n ⋖ h (suc n)
        H = ?
        hH-sats-F : Exence-sats F (h , H)
        hH-sats-F = ?
        hH-greedy : GreedilyIntroducesClasses F (h , H)
        hH-greedy = ?

    

---- Extract a normalisation function from a passable Filter.
--extract-maxclass-nf
--    : {F : Filter}
--    → Passable F
--    → Σ[ f ∈ NFFun ] (NFFun-sats F f ) × (MaximisesClasses F f)
--extract-maxclass-nf {F} pass = (f' , f-stats-F , f-max-classes)
--    where
--        E : Exence
--        E = proj₁ pass

--        f' = combine E

--        --f : ℕ → ℕ
--        --f = ?

--        --f-leq : (n : ℕ) → f n ≤ n
--        --f-leq n = ?

--        --f-fix : (n : ℕ) → f (f n) ≡ f n
--        --f-fix n = ?

--        --f' : NFFun
--        --f' = (f , f-leq , f-fix)

--        --f-stats-F : (Filter-sats F f' )
--        --f-stats-F = ?

--        f-max-classes : (MaximisesClasses F f')
--        f-max-classes = ?


