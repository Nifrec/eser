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


--------------------------------------------------------------------------------
-- Signoids
-- Generalisation of signatures with finitely many constructors
-- of finite arity.
-- Elsewhere we describe how to extract two relations from arbitrary signatures:
--  * A lexicographical ordering, i.e., a chain, i.e., a decidable enumeration,
--      i.e., a stream of all the elements of the signature.
--  * A subterm relation.
--  
-- When we isolate those relations, we obtain the more general 'signoids'
-- that only have the properties needed for building a StreamGrid from it.
--------------------------------------------------------------------------------

-- Strict `<` relations of the form `x_1 < x_2 < x_3 < ...`.
-- AKA 'linear orders'.
Chain 
    : {A : Set} 
    → Rel A 0ℓ 
    → Set
Chain {A} _<_ 
    = (Transitive _<_)
    × (Irreflexive _≡_ _<_)
    × (Total _<_)
    × (Asymmetric _<_)

-- The elements of order (A, <) can be iterated: 
-- there is an enumeration `f : ℕ → A` monotone in <.
-- Note: if _<_ is a chain then (1) surjectivity plus (2) monoticity 
-- of f imply injectivity (i.e., every element has a *unique* index).
data Enumeration (A : Set) (_<_ : Rel A 0ℓ) : Set where
    -- If A has only finitely many elements:
    finEnum : 
        Σ[ n ∈ ℕ ] (
        Σ[ f ∈ (Fin n → A) ] (
        ((a : A) → Σ[ m ∈ Fin n ](a ≡ f m))
        ×
        ((m m' : Fin n) → (f m < f m'))
        )
        )
        → Enumeration A _<_
    -- If A has countably infinitely many elements:
    infEnum : 
        Σ[ f ∈ (ℕ → A) ] (
        ((a : A) → Σ[ m ∈ ℕ ](a ≡ f m))
        ×
        ((m m' : ℕ) → (f m < f m'))
        )
        → Enumeration A _<_

-- Extract enumeration function out of an enumerated linear order.
getEnumerator 
    : {A : Set} 
    → {_<_ : Rel A 0ℓ}
    → (c : Chain _<_)
    → (e : Enumeration A _<_)
    → ℕ 
    → A
getEnumerator c e n = ?

-- Lookup the index of an element in an enumerated linear order.
getIndex 
    : {A : Set} 
    → {_<_ : Rel A 0ℓ}
    → (c : Chain _<_)
    → (e : Enumeration A _<_)
    → (a : A)
    → Σ[ n ∈ ℕ ] ((getEnumerator c e) n ≡ a)
getIndex c e a = ?

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
        → (σ    : Enumeration A _<_)
        --→ (_⊂_  : Rel A 0ℓ)
        → (p    : SubRelat _<_ _⊂_)
        → NiceProperties _⊂_
        → Signoid A _<_ _⊂_

