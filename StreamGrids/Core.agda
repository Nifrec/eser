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

