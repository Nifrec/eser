-- Module      : Eser.Sum
-- Description : Extra properties about _*_ on ℕ.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
{-# OPTIONS --safe #-}

open import Level hiding (suc)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Function hiding (_↔_)

module Eser.Mult where

-- The standard library has *-suc : m * (suc n) ≡ m + m * n.
-- This is the same up to commutativity of _+_ and _*_.
*-suc' 
    : (m n : ℕ)
    → (suc m) * n ≡ m * n + n
*-suc' m n = 
    begin 
        (suc m * n)
    ≡⟨ *-comm (suc m) n ⟩
        n * suc m
    ≡⟨ *-suc n m ⟩
        n + n * m
    ≡⟨ +-comm n (n * m) ⟩
        n * m + n
    ≡⟨ cong (_+ n) $ *-comm n m ⟩
        m * n + n
    ∎
    

