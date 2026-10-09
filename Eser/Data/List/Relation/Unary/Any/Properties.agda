-- Module      : Eser.Data.List.Relation.Unary.Any
-- Description : Additional properties for the 'Any' module of the stdlib.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Data.Nat
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.Sum
open import Function using (_∘_ ; _$_)
open import Data.List using (List ; [] ; _∷_)
open import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.Any.Properties

open import Eser.Aux using (_↔_)

module Eser.Data.List.Relation.Unary.Any.Properties where

Any-⊎-right
    : {A : Set}
    → (P : A → Set)
    → (x : A)
    → (xs : List A)
    → (Any P xs ⊎ P x) ↔ Any P (x ∷ xs)
Any-⊎-right {A} P x xs = (to , from)
    where
        to : Any P xs ⊎ P x → Any P (x ∷ xs)
        to (inj₁ Pxs) = Any.there Pxs
        to (inj₂ Px)  = Any.here Px
        from : Any P (x ∷ xs) → Any P xs ⊎ P x
        from (Any.here Px) = inj₂ Px
        from (Any.there Pxs) = inj₁ Pxs

