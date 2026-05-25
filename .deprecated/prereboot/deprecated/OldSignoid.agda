-- Module      : StreamGrids.Signoid
-- Description : Definition and lemmas of Signoids
-- Copyright   : (c) Lulof Pirée, 2025
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}
module StreamGrids.Signoid where

-- TODO: probably not all of these are needed.
open import Data.Bool hiding (_≤_; _≤?_)
open import Data.Empty
open import Data.Fin hiding (_<_)
open import Function using (Inverseᵇ)
open import Data.List
open import Data.Nat hiding (_<_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Level using (0ℓ)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
open import Relation.Nullary

-- The ones below are certainly needed.
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Linked using (Linked)
-- Implementation note: Data.List.Relation.Unary.Sorted.TotalOrder
-- gives `Sorted` instead of `Linked`, but it only works with reflexive
-- total orders, and _«_ is always irreflexive.

open import StreamGrids.Chain
open import StreamGrids.Card
--open import StreamGrids.List

--------------------------------------------------------------------------------
-- Auxiliary definitions
--------------------------------------------------------------------------------
-- Biimplication A ←→ B : two types can prove each other.
_iff_ : {ℓ : Level.Level} → (A B : Set ℓ) → Set ℓ
A iff B = (A → B) × (B → A)


--------------------------------------------------------------------------------
-- Signoids
-- The raw "strings" that we later (when building a StreamGrid on top of it)
-- will quotient by equalities to obtain our desired type.
--
-- For example, a finitely generated monoid over {a, b} is (1) a signature
-- with three nullary constructors (the unit, a and b),
-- and one binary constructor _·_ ,
-- together with (2) equalities between the signature's terms
-- (e.g., ensuring (a·a)·b ≈ a·(a·b), which are *not* equal signature terms,
-- but equal as monoid elements.
--
-- Signoids are generalisation of, among others, the following things:
--  * Strings over a fixed alphabet.
--  * Signatures with finitely many constructors of finite arity.
--  * Enumerable inductive types.
--
-- There are two ways to give a signoid A.
-- Both ways give an enumeration `enum : ℕ → A` and a 'subterm relation'
-- `_⊂_ : A → A → Type` such that `x ⊂ y` ensures `enum x < enum y`.
-- (I.e., subterms have lower numbers).
-- The last piece is either
-- 1. an inverse to `enum`.
-- or
-- 2. a relation _<_ that is a Chain and a superrelation of _⊂_,
--  s.t. `enum` is also monotone in _<_.
--
-- The data pieces 1. and 2. can be constructed from each other,
-- so only one of the two is strictly necessary.
-- However, these canonical constructions are not efficiently implemented:
-- they are brute-force enumerate till you found the desired number,
-- and `(x, y) ↦ enum x < enum y`, respectively.
-- Therefore we allow the user is allowed to 
-- provide custom (optimised) implementations for both if they so desire.
--------------------------------------------------------------------------------
--------------------------------------------------------------------------------
-- Subterm relations
--------------------------------------------------------------------------------
-- Intuition in the context of signatures:
-- if `c(a)` is a term consisting of constructor `c` 
-- taking argument `a` (a tree),
-- and there exist a smaller tree `a'`, then `c(a')` is also an existing term,
-- and in the lexicographical order we have `c(a') < c(a)`.
-- In general, _⊂_ is a subterm relation of _<_ if:
-- (1) it is a subrelation,
-- (2) it has the subterm property:
--      if `x ⊂ y` and `x' < x`, then there exists a `y'` with the same
--      ⊂-children as `y`, except for also having `x'` and possibly not `x`,
--      and `y' < y`.

-- There is a definiton `SubRelation` in `Relation.Binary.Reasoning.Syntax`
-- but it is notationally too cumbersome (_S_ would be hidden in a 
-- huge record, making it difficult to get an infix _S_ without pattern-matching
-- the whole record every time).
IsSubRelat 
    : {ℓ : Level.Level}
    → {A : Set ℓ}
    → Rel A ℓ 
    → Rel A ℓ
    → Set ℓ
IsSubRelat {ℓ} {A} _R_ _S_ = {x y : A} → x S y → x R y

-- See "Lessons learned" in README.md.
-- #TODO: ref to more docu about this.
SubtermCoercion
    : {ℓ : Level.Level}
    → {A : Set ℓ} 
    → (_<_ : Rel A ℓ)
    → (_⊂_ : Rel A ℓ)
    → Set ℓ
SubtermCoercion {ℓ} {A} _<_ _⊂_ =
    {y x x' : A} 
        → (x ⊂ y) → (x' < x) 
        --^ If y has a subterm x for which an alternative, lexicographically
        -- smaller choice x' also exists, ...
        → Σ[ y' ∈ A ](
        --^ ...then there exists a coercion y' of y, ...
        (y' < y)
        --^ ...which is lexicographically smaller...
        × (x' ⊂ y') × ¬ (x ⊂ y')
        --^ ...and which has subterm x' instead of x...
        × ({x'' : A} → (x'' ≢ x) → (x'' ≢ x') → ((x'' ⊂ y) iff (x'' ⊂ y')))
        --^ ... but the other subterms of y' are the same as for y.
        )
--------------------------------------------------------------------------------
-- Actual definition of Signoid and constuction methods.
--------------------------------------------------------------------------------

record Signoid 
    {ℓ : Level.Level} 
    {A : Set ℓ} 
    (_<_ : Rel A ℓ) 
    (_⊂_ : Rel A ℓ) 
    : Set ℓ where
    field
        numEl    : ℕ∞
        enum     : (cardToSet numEl) → A
        mono : Monotonic₁ (cardTo<) (_<_) enum
        surj     : (a : A) → Σ[ n ∈ cardToSet numEl ]( enum n ≡ a)
        chain : Chain _<_
        subrelat : IsSubRelat _<_ _⊂_
        coercion : SubtermCoercion _<_ _⊂_ 
        getIdx : A → cardToSet numEl
        inv : Inverseᵇ _≡_ _≡_ enum getIdx

-- The `getIdx` and `inv` fields can be distilled from the other data,
-- just brute force enumerate until you found the desired term.
record ChainPreSignoid 
    {ℓ : Level.Level} 
    {A : Set ℓ} 
    (_<_ _⊂_ : Rel A ℓ) 
    : Set ℓ where
    field
        numEl    : ℕ∞
        enum     : (cardToSet numEl) → A
        mono : Monotonic₁ (cardTo<) (_<_) enum
        surj     : (a : A) → Σ[ n ∈ cardToSet numEl ]( enum n ≡ a)
        chain : Chain _<_
        subrelat : IsSubRelat _<_ _⊂_
        coercion : SubtermCoercion _<_ _⊂_ 

chainPreToSignoid 
    : {ℓ : Level.Level} {A : Set ℓ} {_<_ _⊂_ : Rel A ℓ}
    → ChainPreSignoid _<_ _⊂_ 
    → Signoid _<_ _⊂_
chainPreToSignoid sig = record { 
    numEl = ChainPreSignoid.numEl sig ; 
    enum = ChainPreSignoid.enum sig ; 
    mono = ChainPreSignoid.mono sig ;
    surj = ChainPreSignoid.surj sig ;
    chain = ChainPreSignoid.chain sig ;
    subrelat = ChainPreSignoid.subrelat sig ;
    coercion = ChainPreSignoid.coercion sig ;
    getIdx = {! !} ;
    inv = {! !} 
    }
