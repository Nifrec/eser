-- Module      : Eser.Vec
-- Description : Additional properties of Vec.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
open import Level hiding (suc)
--open import Data.Bool using (Bool ; true) renaming (T to IsTrue)
open import Data.Nat
open import Data.Nat.Properties
--open import Data.Sum hiding (reduce ; map)
--open import Data.Product hiding (map)
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
--open ≡-Reasoning -- renaming (begin_ to ≡begin_ ; _∎ to _≡∎)
open import Relation.Unary using (_⊆_)
open import Data.Vec
--open import Data.Vec.Membership.Propositional
--open import Data.Vec.Relation.Unary.All as All hiding (_∷_ ; head ; tail)
--open import Data.Vec.Relation.Unary.Any as Any hiding (head ; tail)
open import Function hiding (_↔_)

module Eser.Vec where

-- Replace all occurrences of one element in a vector by another element.
replace-all : {A : Set}
    → (_≡?_ : DecidableEquality A)
    → {n : ℕ}
    → (v : Vec A n)
    → A -- Element to replace all occurrences of.
    → A -- Replacement.
    → Vec A n
replace-all {A} _≡?_ v a b = map f v
    where
        f : A → A
        f x = cases (x ≡? a)
            where
                cases : (Dec (x ≡ a)) → A
                cases (yes refl) = b
                cases (no _) = x

