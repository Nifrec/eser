-- Module      : StreamGrids.NewSignoid
-- Description : Updated definition (8 Dec 2025 version) of Signoids
-- Copyright   : (c) Lulof Pirée, 2025
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}
module StreamGrids.NewSignoid where

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
open import Relation.Nullary

-- The ones below are certainly needed.
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Unary.Linked using (Linked)
-- Implementation note: Data.List.Relation.Unary.Sorted.TotalOrder
-- gives `Sorted` instead of `Linked`, but it only works with reflexive
-- total orders, and _«_ is always irreflexive.

open import StreamGrids.Chain
open import StreamGrids.Card
--open import StreamGrids.List

-- #TODO: import and update and extend relevant comments from old Signoid.agda.
-- #TODO: while doing so, rename 'subterm-relation' → 'argument-relation'.
--------------------------------------------------------------------------------
-- Actual definition of Signoid 
--------------------------------------------------------------------------------

record Signoid 
    {ℓ : Level.Level} 
    {A : Set ℓ} 
    (_⊂_ : Rel A ℓ) 
    : Set ℓ where
    field
        card     : ℕ∞
        idxToEl  : (cardToSet card) → A
        elToIdx  : A → cardToSet card
        inv : Inverseᵇ _≡_ _≡_ idxToEl elToIdx
        subrelat : (x y : A) → x ⊂ y → (cardTo< (elToIdx x) (elToIdx y))
        --^ This just says that _⊂_ is a subrelation of _«_, i.e.,
        -- that x ⊂ y → x « y. But _«_ is not defined yet here, see below.
        coerc    : (y x : A) → x ⊂ y → (x' : A) → x' ⊂ x → Σ[ y' ∈ A ](
            (cardTo< (elToIdx y') (elToIdx y)))
        --^ As for the previous constructor, just `y' « y`.

enumOrder : 
    {ℓ : Level.Level} 
    {A : Set ℓ} 
    {_⊂_ : Rel A ℓ} 
    {S : Signoid _⊂_}
    → Rel A _
enumOrder {ℓ} {A} {_⊂_} {S} x y 
    = cardTo< {Signoid.card S} (Signoid.elToIdx S x) (Signoid.elToIdx S y)

infix 30 enumOrder
syntax enumOrder x y = x « y
