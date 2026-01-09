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

open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin
open import Data.Fin.Properties

-- Local imports.
open import StreamGrids.Card


module StreamGrids.Addibles where

    Addibles : (c : ℕ∞) → (n : cardToSet c) → Set
    Addibles ∞ n = ℕ
    Addibles (fin zero) ()
    Addibles (fin (ℕ.suc c)) n = Fin (ℕ.suc c ∸ toℕ n)

    -- Add an addible to n while staying in `cardToSet c`.
    add : (c : ℕ∞) → (n : cardToSet c) → Addibles c n → cardToSet c
    add ∞ n m = n Data.Nat.+ m
    add (fin zero) ()
    add (fin (suc c)) n m = 
        let meh : toℕ n Data.Nat.≤ ℕ.suc c
            meh = Data.Fin.Properties.toℕ≤n n
        in
        let lemma : toℕ n Data.Nat.+ (ℕ.suc c ∸ toℕ n) ≡ ℕ.suc c
            lemma = Data.Nat.Properties.m+[n∸m]≡n meh
        in
        let out : Fin (ℕ.suc c)
            out = cast lemma (n Data.Fin.+ m) 
        in
        out
