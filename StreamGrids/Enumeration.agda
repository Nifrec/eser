-- Module      : StreamGrids.Enumeration
-- Description : Definition and tool for enumarable types
-- Copyright   : (c) Lulof Pirée, 2025
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------

module StreamGrids.Enumeration where

-- #TODO: probably not all of these are needed.
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

_<ℕ_ : Rel ℕ 0ℓ
n <ℕ m = n Data.Nat.< m
infixl 10 _<ℕ_

-- Natural numbers extended with a top element '∞' (w.r.t. the '<' relation).
-- #TODO: check if this already exist in the standard library?
data ℕ∞ : Set where
    fin     : ℕ → ℕ∞
    ∞       : ℕ∞

_<∞_ : Rel ℕ∞ 0ℓ
fin n <∞ fin m  = n <ℕ m
fin n <∞ ∞      = ⊤
∞     <∞ fin m  = ⊥
∞     <∞ ∞      = ⊥

-- The elements of ordered set (A, <) can be iterated: 
-- there is an enumeration `f : ℕ → A` monotone in <.
-- Note: in the typical use case where _<_ is a chain,
-- the (1) surjectivity plus (2) monoticity 
-- of `enum` imply injectivity (i.e., every element has a *unique* index).
record ChainEnum {ℓ : Level.Level} {A : Set ℓ} (_<_ : Rel A ℓ) (_≈_ : Rel A ℓ) 
    : Set ℓ where
    field
        numEl    : ℕ∞
        enum     : ℕ → A
        monotone : (n : ℕ) → ((fin (suc n)) <∞ numEl) → enum n < enum (suc n)
        surj     : (a : A) → Σ[ n ∈ ℕ ]( (fin n <∞ numEl) × (enum n ≈ a) )
-- Implementation note: 
-- in case `numEl` is finite, then there may exist different
-- enumerations f,g : ℕ → A whose restruction to [0, 1, 2, ..., numEl-1]
-- coincides.
-- This can be avoided by adding an additional constraint, e.g.,
-- requiring all greater values to be mapped to some `error` output:
-- f : ℕ → A ⊎ ⊤
-- and requiring (n ≥∞ numEl) → (f n = inr tt)`.
-- It is not done here, as (1) there is no strict need, 
-- and (2) to keep things simpler.
    
-- #TODO: implement setters & getters
-- Lookup the index of an element in an enumerated linear order.
--getIndex 
--    : {A : Set} 
--    → {_<_ : Rel A 0ℓ}
--    → (c : Chain _<_)
--    → (e : Enumeration A _<_)
--    → (a : A)
--    → Σ[ n ∈ ℕ ] ((getEnumerator c e) n ≡ a)
--getIndex c e a = ?

record InvertibleEnum {ℓ : Level.Level} {A : Set ℓ} (_<_ : Rel A ℓ) (_≈_ : Rel A ℓ) 
    : Set ℓ where
    field
        numEl    : ℕ∞
        enum     : ℕ → A
        getIdx   : A → ℕ


--------------------------------------------------------------------------------
-- Unused alternative ideas for defining `Enumeration`.
--------------------------------------------------------------------------------

private

    -- The elements of order (A, <) can be iterated: 
    -- there is an enumeration `f : ℕ → A` monotone in <.
    -- Note: if _<_ is a chain then (1) surjectivity plus (2) monoticity 
    -- of f imply injectivity (i.e., every element has a *unique* index).
    data Enumeration2 (A : Set) (_<_ : Rel A 0ℓ) : Set where
        -- If A has only finitely many elements:
        finEnum : 
            Σ[ n ∈ ℕ ] (
            Σ[ f ∈ (Fin n → A) ] (
            ((a : A) → Σ[ m ∈ Fin n ](a ≡ f m))
            ×
            ((m m' : Fin n) → (f m < f m'))
            )
            )
            → Enumeration2 A _<_
        -- If A has only finitely many elements:
        finEnum2 : 
            Σ[ n ∈ ℕ ] (
            -- ^ Number of elements of A ≅ [0, 1, ..., n-1].
            Σ[ f ∈ (ℕ → A) ] (
            ((a : A) → Σ[ m ∈ ℕ ]((m <ℕ n) × (a ≡ f m)))
            ×
            ((m m' : ℕ) → (m <ℕ m') → (m' <ℕ n) → (f m < f m'))
            )
            )
            → Enumeration2 A _<_
        -- If A has countably infinitely many elements:
        infEnum : 
            Σ[ f ∈ (ℕ → A) ] (
            ((a : A) → Σ[ m ∈ ℕ ](a ≡ f m))
            ×
            ((m m' : ℕ) → (m <ℕ m') → (f m < f m'))
            )
            → Enumeration2 A _<_

    ---- Extract enumeration function out of an enumerated linear order.
    --getEnumerator 
    --    : {A : Set} 
    --    → {_<_ : Rel A 0ℓ}
    --    → (c : Chain _<_)
    --    → (e : Enumeration2 A _<_)
    --    → ℕ 
    --    → A
    --getEnumerator c e n = ?

    ---- Lookup the index of an element in an enumerated linear order.
    --getIndex 
    --    : {A : Set} 
    --    → {_<_ : Rel A 0ℓ}
    --    → (c : Chain _<_)
    --    → (e : Enumeration2 A _<_)
    --    → (a : A)
    --    → Σ[ n ∈ ℕ ] ((getEnumerator c e) n ≡ a)
    --getIndex c e a = ?

