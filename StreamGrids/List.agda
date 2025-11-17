-- Module      : StreamGrids.List
-- Description : Auxiliary functions for lists
-- Copyright   : (c) Lulof Pirée, 2025
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
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
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

open import Function.Base using (_∘_)

module StreamGrids.List where

--------------------------------------------------------------------------------
-- Indicing in a List A.
--------------------------------------------------------------------------------
module SingleIndex 
    {ℓ : Level.Level}
    {A : Set ℓ}
    where

    Indices : List A → Set
    Indices L = Fin (length L)

    getEl : (L : List A) → Indices L → A
    getEl [] ()
    getEl (x ∷ xs) zero = x
    getEl (x ∷ xs) (suc i) = getEl (xs) i

    -- Left associative notation for indexing lists.
    -- So a list of lists can now be indexed as `L ,, i ,, j`.
    _,,_ : (L : List A) → Indices L → A
    L ,, i = getEl L i
    infixl 30 _,,_

    -- A proof of membership of an element is an index at which the element occurs.
    _∈_ : A → List A → Set ℓ
    a ∈ L = Σ[ i ∈ (Indices L) ]( L ,, i ≡ a)
    infixr 30 _∈_

    -- Get the index of an element of which we know it exists in the list.
    getListIdx : {L : List A} → {a : A} → (a ∈ L) → Indices L
    getListIdx {L} {a} (i , _) = i

open SingleIndex public

--------------------------------------------------------------------------------
-- Double-indiced lists (lists of lists)
--------------------------------------------------------------------------------
module DoubleIndex 
    {ℓ : Level.Level}
    {A : Set ℓ}
    where

    -- Predicate that says that an element occurs in at least one of the sublists.
    -- For example, it holds that:
    --      6 ∈∈ (( 1 ∷ 2 ∷ 3 ∷ [] ) ∷ ( 4 ∷ 5 ∷ 6 ∷ [] ) ∷ [])
    _∈∈_ : A → List (List A) → Set ℓ
    a ∈∈ L = Σ[ i ∈ (Indices L) ](
        Σ[ j ∈ (Indices (L ,, i)) ]( L ,, i ,, j ≡ a)
        )
    infixr 30 _∈∈_

    -- Total number of elements in a doubly indexed list.
    flatLength : List (List A) → ℕ
    flatLength = length ∘ concat

open DoubleIndex public
