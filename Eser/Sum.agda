-- Module      : Eser.Sum
-- Description : General properties about Data.Sum
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
{-# OPTIONS --safe #-}

open import Level hiding (suc)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Function hiding (_↔_)

module Eser.Sum where

    module _ {A B : Set} where
        
        -- `inj₁ a ≡ inj₂ b` is always impossible.
        sum-disjoined
            : {a : A}
            → {b : B}
            → _≡_ {A = A ⊎ B} (inj₁ a) (inj₂ b)
            → ⊥
        sum-disjoined ()

