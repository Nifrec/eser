-- Module      : StreamGrids.Core
-- Description : Core definitions and functions
-- Copyright   : (c) Lulof Pirée, 2025
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- Contents of this file:

module StreamGrids.Core where

-- TODO: probably not all of these are needed.
open import Data.Bool hiding (_≤_; _≤?_)
open import Data.Empty
open import Data.Fin
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.String
open import Data.Sum
open import Data.Unit
open import Data.Vec
open import Level using (0ℓ)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

open import StreamGrids.Chain
open import StreamGrids.Enumeration

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

SubRelat 
    : {A : Set} 
    → Rel A 0ℓ 
    → Rel A 0ℓ 
    → Set
SubRelat {A} _<_ _⊂_ = ?

NiceProperties 
    : {A : Set} 
    → Rel A 0ℓ 
    → Set
NiceProperties {A} _⊂_ = ?

data Signoid (A : Set) (_<_ : Rel A 0ℓ) (_⊂_ : Rel A 0ℓ) : Set where
    mkSignoid 
        --: (_<_  : Rel A 0ℓ) 
        : (c    : Chain _<_)
        → (σ    : Enumeration A _<_ _≡_)
        --→ (_⊂_  : Rel A 0ℓ)
        → (p    : SubRelat _<_ _⊂_)
        → NiceProperties _⊂_
        → Signoid A _<_ _⊂_

