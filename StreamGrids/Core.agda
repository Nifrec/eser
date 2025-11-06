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
open import Relation.Binary.Reasoning.Syntax using (SubRelation)

-- #TODO: this definition is still WIP,
-- the type may change (maybe enum is needed).
IsSubTermRelat 
    : {ℓ : Level.Level}
    → {A : Set ℓ} 
    → (_<_ : Rel A ℓ)
    → SubRelation _<_ ℓ ℓ
    → Set ℓ
IsSubTermRelat {A} _⊂_ = ?

--InverseOfEnum : {ℓ : Level.Level} {A : Set ℓ} (e : Enumeration _<_ _≡_) → Set ℓ
--InverseOfEnum = ?

-- Map a cardinality in Bigℕ to the prefix of the natural numbers
-- with that cardinality.
cardToSet : ℕ∞ → Set
cardToSet (fin 0) = ⊥
cardToSet (fin (suc n)) = Fin (suc n) -- Fin 0 cannot be constructed!
cardToSet ∞ = ℕ
 
-- Get the default < relation on a prefix of ℕ.
cardTo< : (n : ℕ∞) → Rel (cardToSet n) 0ℓ
cardTo< (fin 0) ()
cardTo< (fin (suc n)) = Data.Fin._<_
cardTo< ∞ = Data.Nat._<_

cardToMax : (n : ℕ∞) → cardToSet n
cardToMax (fin 0) ()
cardToMax (fin (suc n)) = fromℕ n
cardToMax 

cardToSuc : {n : ℕ∞} → (m : cardToSet n) → (m (cardTo< n) ?) → cardToSet n 
cardToSuc {fin 0} ()
cardToSuc {fin (suc n)} m m<∞n = Data.Fin.suc m
cardToSuc {∞} m m<∞n = Data.Nat.suc m

--record PreEnum {ℓ : Level.Level} {A : Set ℓ} (_≈_ : Rel A ℓ) : Set ℓ where
--    field
--        numEl    : ℕ∞
--        enum     : ℕ → A
--        monotone : (n : ℕ) → ((fin (suc n)) <∞ numEl) → enum n < enum (suc n)
--        surj     : (a : A) → Σ[ n ∈ ℕ ]( (fin n <∞ numEl) × (enum n ≈ a) )
---- Implementation note: 
---- in case `numEl` is finite, then there may exist different
---- enumerations f,g : ℕ → A whose restruction to [0, 1, 2, ..., numEl-1]
---- coincides.
---- This can be avoided by adding an additional constraint, e.g.,
---- requiring all greater values to be mapped to some `error` output:
---- f : ℕ → A ⊎ ⊤
---- and requiring (n ≥∞ numEl) → (f n = inr tt)`.
---- It is not done here as there is no real need for introducing additional
---- complexity.

record Signoid 
    {ℓ : Level.Level} 
    {A : Set ℓ} 
    (_<_ : Rel A ℓ) 
    (_⊂_ : SubRelation _<_ ℓ ℓ) 
    : Set ℓ where
    field
        numEl    : ℕ∞
        enum     : (cardToSet numEl) → A
        monotone : (n : (cardToSet numEl)) → (enum n) < (enum (cardToSuc numEl n))
        --surj     : (a : A) → Σ[ n ∈ ℕ ]( (fin n <∞ numEl) × (enum n ≈ a) )
        chain : Chain _<_
        subterm : IsSubTermRelat _<_ _⊂_ 
        --getIdx : InverseOfEnum enum
