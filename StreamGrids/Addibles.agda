-- Module      : StreamGrids.Addibles
-- Description : Type of numbers you can still add to a given number
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- Use case: you want to inductively prove P(i)
-- for all i ≥ j for some `j ∈ cardToSet c`.
-- The strategy is then to prove P(j + a) for all compatible `a`,
-- by inudction on a.
-- But how do we do induction on a?
-- Well, if c ≐ ∞ then a ∈ ℕ and we can just do induction on ℕ.
-- If c ≐ fin (suc c') then we can still find some finite set
-- of numbers that can be added to j without overshooting
-- the finite set `Fin (suc c')` in which j and j+a live.

open import Level
open import Relation.Binary hiding (Irrelevant)
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Product
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum
open import Data.Fin
open import Data.Fin.Properties
open import Data.Unit
open import Data.Empty
open import Data.List
open import Data.List.Relation.Unary.AllPairs using (AllPairs)
open import Data.List.Relation.Unary.All using (All)
open import Data.List.Relation.Binary.Suffix.Heterogeneous using (Suffix)
open import Data.List.Membership.Propositional using (_∈_ ; _∉_ )
open import Data.List.Membership.Propositional.Properties using (∈-lookup)
open import Data.List.Relation.Unary.Any using (Any)

-- Local imports.
open import StreamGrids.Card
open import StreamGrids.Logic
open import StreamGrids.Fin


module StreamGrids.Addibles where

    Addibles : (c : ℕ∞) → (n : cardToSet c) → Set
    Addibles ∞ n = ℕ
    Addibles (fin zero) ()
    Addibles (fin (suc c)) n = Fin (toℕ (opposite n))

    -- Add an addible to n while staying in `cardToSet c`.
    add : (c : ℕ∞) → (n : cardToSet c) → Addibles c n → cardToSet c
    add ∞ n m = n Data.Nat.+ m
    add (fin zero) ()
    add (fin (suc c)) n m = 
        -- toℕ (opposite n) ≡ ℕ.suc c - ℕ.suc (toℕ n)
        let m' : Fin (ℕ.suc c ∸ ℕ.suc (toℕ n))
            m' = cast (Data.Fin.Properties.opposite-prop {ℕ.suc c} n) m
        in
        let out = n Data.Fin.+ m'
        in

        {! (n Data.Fin.+ m) !}
