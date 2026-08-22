-- Module      : Eser.SigStream.EnumStream
-- Description : Streams that enumerate a type.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- 𝐄𝐧𝐮𝐦𝐒𝐭𝐫𝐞𝐚𝐦(A)
--  Stream that includes every term of A exactly once.
--------------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Level hiding (suc)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Function hiding (_↔_)
open import Codata.Guarded.Stream

open import Eser.Aux using (_↔_)
open import Eser.Equivalences.Notation

module Eser.SigStream.EnumStream where

    -- Uniqueness : every element of A occurs at most once in the stream.
    -- We define it as "lookup is injective".
    Unique : {A : Set} → (s : Stream A) → Set
    Unique {A} s = (n m : ℕ) → lookup s n ≡ lookup s m → n ≡ m

    -- Completeness : every element of A occurs at least once in the stream.
    -- We define it as "lookup is surjective".
    Complete : {A : Set} → (s : Stream A) → Set
    Complete {A} s = (a : A) → Σ[ n ∈ ℕ ] lookup s n ≡ a

    isEnumStream : {A : Set} → (s : Stream A) → Set
    isEnumStream s = Unique s × Complete s

    -- There exists an enumeration stream for A iff A is equivalent to ℕ.
    theorem-enumStream 
        : {A : Set}
        → (Σ[ s ∈ Stream A ] isEnumStream s) ↔ (A ≃ ℕ)
    theorem-enumStream {A} = (f , g)
        where
            f : Σ[ s ∈ Stream A ] isEnumStream s → (A ≃ ℕ)
            f (s , unique , complete) = ?

            g : (A ≃ ℕ) → Σ[ s ∈ Stream A ] isEnumStream s
            g = ?

