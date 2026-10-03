-- Module      : Eser.Filters.Composition
-- Description : Composing Filters and properties of composition.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- Filter composition is NOT just pointwise ∧, as the ∧ of two dead-end-free
-- filters may very well have a dead end (i.e., be unsatisfiable, i.e., not
-- allowing *any choice* for some inputs).
--
-- However, we know that we can always take the congruence closure of a
-- relation. A relation R can be encoded as a filter F_R that allows only the
-- choices in R, so it is only satisfied by R.
-- We want to define a (non-symmetric) composition _»_ such that
-- F_R » P computes the P-closure of R (actually the filter that only allows
-- the relation that is the P-closure of R), where P is some dead-end-free
-- predicate like congruence.
--
-- We first adapt the definition of a Filter.
-- Instead of directly telling (via a Bool) for each choice of extending
-- an r : NFRestr n whether or not it is allowed, a Filter first tells whether
-- or not it 'fires' given r. If it fires, it behaves as usual.
-- If it doesn't fire (if it 'passes'), 
-- then we interpret that "every choice is OK, I don't care".
--
-- The composition G » F on input r returns (F r) : Choices r → Bool
-- if F fires on input r. If F passes on input r, but G fires on input r,
-- then we return (G r) : Choices r → Bool.
-- If both filters pass, then we accept all choices (so return (λ _ → true) :
-- Choices r → Bool).
--
-- This _»_ composition turns MayFireFilters into an idempotent non-commutative 
-- monoid, with the filter that always passes as unit.
-- The non-commutativity feels surprising, since combining predicates
-- on relations directly can be done via the commuting ∧,
-- but here the order does matter.
--
-- Note that passing is NOT the same as firing and then returning true on all
-- inputs, since passing goes to the next filter in the composition,
-- whereas firing gives a definite verdict on whether a choice is allowed.
-- Outside compositions, when the filter is used alone,
-- both options do behave identically though.
--------------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Data.Nat
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Nullary
open import Data.Product
open import Data.Sum
open import Function using (_∘_ ; _$_)
--open import Data.Nat.Properties using 
--    (m<1+n⇒m<n∨m≡n 
--    ; n<1+n 
--    ; <-irrefl 
--    ; m≤n⇒m<n∨m≡n
--    ; <-trans
--    ; n≮n
--    ; <-irrelevant
--    ; suc-injective
--    ; ≤-refl
--    ; ≤-trans
--    ; n≤1+n
--    ; ≤-<-trans
--    )

open import Eser.EqRel.Definitions using (NFFun) renaming (DecEquiv to EqRel)
open import Eser.EqRel.Conversions using (RelToFun)
open import Eser.Aux using (_≈_ ; _↔_ )
open import Eser.Filters.Conversions.NFFunToExence

open import Eser.Filters.Base
open import Eser.Filters.Properties
open import Eser.Filters.PointwiseProperties

module Eser.Filters.Composition where

--------------------------------------------------------------------------------
-- MayFireFilters
--------------------------------------------------------------------------------

-- Functor isomorphic to 'Maybe', but I use a different name to avoid confusion
-- with Maybe's well-known monadic Kleisli composition (which is NOT _»_
-- composition!).
data MayFire (A : Set) : Set where
    fire : A → MayFire A
    pass : MayFire A

MayFireFilter : Set
MayFireFilter = 
      {n : ℕ}
    → (r : NFRestr n)
    → MayFire(Choices r → Bool)

MFF = MayFireFilter

-- How we interpret a MayFireFilter as a Filter: passing means allowing all
-- choices.
MFF→Filter : MayFireFilter → Filter
MFF→Filter F {n} r c = cases (F r) c
    where
        cases : MayFire (Choices r → Bool) → Choices r → Bool
        cases (fire f) c = f c
        cases pass _ = true

-- Always fire.
Filter→MFF : Filter → MayFireFilter
Filter→MFF F r = fire (F r)

--------------------------------------------------------------------------------
-- _»_ : MayFireFilter composition
--------------------------------------------------------------------------------
-- Right associativity: H » G » F ≔ H » (G » F). 
-- Not that it really matters since _×_ is associative anyway.
infixr 70 _»_

_»_ : MFF → MFF → MFF
(G » F) r = cases (F r)
    where   
        cases : MayFire (Choices r → Bool) → MayFire (Choices r → Bool)
        cases (fire f) = fire f
        cases pass = G r

-- _»_ is associative (up to function extensionality).
»-assoc : (H G F : MFF) → (H » G) » F ≈ H » (G » F)
»-assoc = {! TODO : Only prove if needed / if supervisors care. 
             Idem for units and unit laws. !}

--------------------------------------------------------------------------------
-- Filter encoding of a relation
--------------------------------------------------------------------------------

-- 'Same NFFun' up to function extensionality.
-- Defined as homotopy between underlaying ℕ → ℕ functions.
_≈≈_ : NFFun → NFFun → Set
(g , _ , _) ≈≈ (f , _ , _) = g ≈ f

-- The imported _≡?_ from Filters.Properties gives 
-- decidable equality on NFS r for any r : NFRestr n.
-- But we also want to compare NFRestr themselves!
_≡NFRestr?_ : {n : ℕ} → DecidableEquality (NFRestr n)
r ≡NFRestr? s = ?

filterify : NFFun → Filter
filterify f {n} r = cases (restrict f n ≡NFRestr? r)
    where
        cases 
            : (Dec (restrict f n ≡ r)) 
            → Choices r 
            → Bool
        cases (yes refl) c = does (f-choice ≡? c)
            where
                f-choice : Choices (restrict f n)
                f-choice = getChoiceFromExence (restrict+ f) n
        -- If r is already different from f, then reject all choices.
        cases (no _) c = false 

MFF-filterify : NFFun → MFF
MFF-filterify = Filter→MFF ∘ filterify

filterify-self-sats
    : (f' : NFFun)
    → NFFun-sats (filterify f') f'
filterify-self-sats f' = ?

-- A Singleton Filter is a filter that is satisfied by exactly one relation.
IsSingleton : Filter → Set
IsSingleton F = 
    Σ[ f ∈ NFFun ] (NFFun-sats F f) × ((g : NFFun) → NFFun-sats F g → g ≈≈ f)

filterify-singleton
    : (f' : NFFun)
    → IsSingleton (filterify f')
filterify-singleton = ?

filterify-deadendfree
    : (f' : NFFun)
    → DeadEndFree (filterify f')
filterify-deadendfree = ?

-- The only NFFun that satisfies `filterify f` is `f` itself (up to function
-- extensionality).
-- This is the specification of `filterify`, so this lemma proves
-- the correctness of `filterify`.
filterify-unique-sat
    : (f' g' : NFFun)
    → NFFun-sats (filterify f') g'
    → g' ≈≈ f'
filterify-unique-sat = {! #TODO: Should be corollary of the above two lemmas !}

--------------------------------------------------------------------------------
-- Definition of P-closure of a relation given a predicate P
--------------------------------------------------------------------------------
-- In set theory it is easy, the P-closure of R is the smallest extension of
-- R that makes it satisfy P.
--
-- It particular, it is the relation R' such that 
-- 1. R ⊆ R'
-- 2. R' satisfies P
-- 3. For all S with R ⊆ S that satisfy P, we have R' ⊆ S.
--
-- This does not exist for all predicates P.
-- For example, if P says "has at least 3 equivalence classes",
-- and R has 2 of them, then there is no extension of R with more than 2
-- equivalence classes (indeed, any new arrow between two elements not yet in R
-- would only collapse the two equivalence classes into one!).
--
-- We formalise the classical definition of the closure,
-- and then characterise the filter-implemented-predicates that are closable.
-- This also comes with an algorithm to 
-- actually compute the closure of a relation.
--
-- In particular, a filter P is a closable predicate if and only if P is
-- 1. One-hot (if it fires, it allows exactly one choice).
-- 2. Dead-end-free.
-- 3. Never forces the unique choice when firing to be newNF.
--
-- The P-closure of a relation R is then simply the unique relation
-- satisfying the singleton filter F_R » P
-- where F_R = Filter→MFF (filterify R).
-- (That that is a singleton does require a lemma).

-- #QUESTION : define this in terms of EqRel or NFFuns?
-- Currently using EqRel since the definition is quite extensional,
-- from an NFFun one cannot immediately tell which elements are related.
-- One can by converting the NFFun to an EqRel or by (1) converting it to an
-- Exence and 
-- (2) using the AreRelated defined in Eser.Filters.NormalityInNFRestr.

Rel-sats : Filter → EqRel → Set
Rel-sats F R = NFFun-sats F (RelToFun R)

_relates_to_ : EqRel → ℕ → ℕ → Set
(R , _) relates x to y = T (R x y)

-- R ⊆ S if S relates all pairs (x, y) that R relates.
_⊆_ : EqRel → EqRel → Set
R ⊆ S = ((x y : ℕ) → R relates x to y → S relates x to y)

_closure-of_ : Filter → EqRel → Set
P closure-of R =
    Σ[ R' ∈ EqRel ]
    R ⊆ R'                                          -- R' is extension of R
    ×
    Rel-sats P R'                                   -- R' satisfies P
    ×
    ((S : EqRel) → R ⊆ S → Rel-sats P S → R' ⊆ S)   -- R' is minimal

--------------------------------------------------------------------------------
-- Uniqueness of P-closure
--------------------------------------------------------------------------------
-- The definition of a closure of a relation already implies it is
-- unique, at least up to function extensionality.
 
-- Extensional equality between relations: 
-- homotopy between the underlying ℕ → ℕ → Bool functions.

_≣_ : EqRel → EqRel → Set
(R , _) ≣ (S , _) = R ≈ S

⊆→⊆→≣ : {R S : EqRel} → R ⊆ S → S ⊆ R → R ≣ S
⊆→⊆→≣ = ?

closure-unique
    : {P : Filter}
    → {R : EqRel}
    → (R' S' : P closure-of R)
    → (proj₁ R') ≣ (proj₁ S')
closure-unique = {! #TODO: use the third property of closure-of, 
    both on R and S, to get R ⊆ S and S ⊆ R, conclude by ⊆→⊆→≣ !}

--------------------------------------------------------------------------------
-- Charactersisation of closable filters
--------------------------------------------------------------------------------

IsClosable : Filter → Set
IsClosable F = (R : EqRel) → F closure-of R

IsClosable' : MFF → Set
IsClosable' F = (R : EqRel) → (MFF→Filter F) closure-of R

DeadEndFree' : MFF → Set
DeadEndFree' = DeadEndFree ∘ MFF→Filter

-- Filters that allow exaclty one choice when they fire.
OneHotFilter : Set
OneHotFilter = {n : ℕ} → (r : NFRestr n) → MayFire (Choices r)

OneHot→MFF : OneHotFilter → MFF
OneHot→MFF F' r = cases (F' r)
    where
        cases : MayFire (Choices r) → MayFire (Choices r → Bool)
        cases pass = pass
        cases (fire c) = fire $ λ c' → does (c ≡? c')

OneHot→Filter : OneHotFilter → Filter
OneHot→Filter = MFF→Filter ∘ OneHot→MFF

-- #QUESTION: could also define as 
-- IsOneHot F = Σ[ F' ∈ OneHotFilter ] F ≈ (OneHot→Filter F')
-- Would that be better?
-- #QUESTION: or remove the definition of 'OneHotFilter' alltogether?
IsOneHot : Filter → Set
IsOneHot F = 
      {n : ℕ} 
    → (r : NFRestr n) 
    → {c c' : Choices r} 
    → F Allows c In r 
    → F Allows c' In r 
    → c ≡ c'

IsOneHot' : MFF → Set
IsOneHot' = IsOneHot ∘ MFF→Filter

-- Sanity check of definition 'OneHotFilter'.
OneHot→IsOneHot : (F : OneHotFilter) → IsOneHot (OneHot→Filter F)
OneHot→IsOneHot = ?

NeverForcesnewNF : Filter → Set
NeverForcesnewNF F = 
      {n : ℕ} 
    → (r : NFRestr n) 
    → (c : Choices r)
    → F Allows c In r
    → c ≢ here

NeverForcesnewNF' : MFF → Set
NeverForcesnewNF' = NeverForcesnewNF ∘ MFF→Filter

-- Big theorem: characterisation of closable predicates (expressed as a filter).
closable-characterisation
    : (F : MFF)
    → (IsClosable' F) ↔ (DeadEndFree' F × IsOneHot' F × NeverForcesnewNF' F)
closable-characterisation = ?

--------------------------------------------------------------------------------
-- Corollary : compositions of closable filters remain closable
--------------------------------------------------------------------------------

-- #TODO: duh, they remain dead-end-free, they remain NeverForcesnewNF, and they
-- remain one-hot. So it follows easily from the previous theorem.

--------------------------------------------------------------------------------
-- Lemma : P-closures of relations satisfying a filter
--------------------------------------------------------------------------------

-- #TODO : If F satisfies 

--------------------------------------------------------------------------------
-- Further notes
--------------------------------------------------------------------------------
-- Maybe the following obervations are worth formalising, maybe not.
-- At least they are important examples for intuition about the usage and limits
-- of filters. Especially useful to mention in a remark when writing a paper.

-- The "has at most 3 equivalence classes" filter is expressible,
-- non trivial and not one-hot. This shows not all usefull filters are
-- necessarily one-hot. (Also works for other numbers than 3, of course).

-- The "has at least 1+n equivalence classes" predicate
-- cannot be expressed as a filter. 

--------------------------------------------------------------------------------
-- Next steps
--------------------------------------------------------------------------------
-- 1. Define 'swap' as a closable filter on replacement structures.
-- 2. Define finite multisets by quotienting List ℕ.
-- 3. Conflict free sets E of equations.
--      - Show they compose to a closeable filter F_E.
--      - Show R sats F_E => R has all equations of E.
--      - Show R' sats F_E » P => <R is the P-closure of a R that has eqs of E>.
-- 4. Correct-by-construction representation or other tool for building such
--    sets of equations.
-- 5. Binay associativity filter, show it is closable.
-- 6. Use 3., 4. and 5. to give a toolbox for building decidable finitely
--    presented monoids.

