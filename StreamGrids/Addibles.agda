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

open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin
open import Data.Fin.Properties
open import Level

-- Local imports.
open import StreamGrids.Card


module StreamGrids.Addibles where

    Addibles : (c : ℕ∞) → (n : cardToSet c) → Set
    Addibles ∞ n = ℕ
    Addibles (fin zero) ()
    Addibles (fin (ℕ.suc c)) n = Fin (ℕ.suc c ∸ toℕ n)
    --Addibles (fin (ℕ.suc c)) n = Fin (ℕ.suc (c ∸ toℕ n))

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

    addℕzero : (n : ℕ) → add ∞ n ℕ.zero ≡ n
    addℕzero n = Data.Nat.Properties.+-identityʳ n

    IsZero : {c : ℕ} → (a : Fin c) → Set
    IsZero {ℕ.zero} _ = ⊥
    IsZero {ℕ.suc c} Fin.zero = ⊤
    IsZero {ℕ.suc (ℕ.suc c)} (Fin.suc a) = ⊥

    -- Adding the successor of an addible a (if it exists)
    -- is the same as adding a first and then taking the successor of the
    -- output.
    addSucCommℕ
        : (n : ℕ)
        → (a : ℕ)
        → add ∞ n (ℕ.suc a) ≡ ℕ.suc (add ∞ n a)
    addSucCommℕ n m = Data.Nat.Properties.+-suc n m

    -- Maybe prove all addibles are of form (suc c ∸ toℕ n) ≡ suc k
    -- and cast Fin.zero from Fin (suc k) to (suc c ∸ toℕ n)?
    --addFinzero : (c : ℕ) → (n : Fin (ℕ.suc c)) → add (fin (ℕ.suc c)) n Fin.zero ≡ Fin.zero

    -- #TODO: deprecate function below, it seems useless
    FinAddiblesRecOld
        : {ℓ : Level}
        → (c : ℕ)
        → (i : Fin (ℕ.suc c))
        → (P : (x : ℕ) → Fin x → Set ℓ)
        → ((x : ℕ) → (a : Fin x) → P x a)
        → ((a : Addibles (fin (ℕ.suc c)) i) → P (ℕ.suc c) (add (fin (ℕ.suc c)) i a))
    FinAddiblesRecOld {ℓ} c i P rec a = rec (ℕ.suc c) (add (fin (ℕ.suc c)) i a)

--------------------------------------------------------------------------------
-- Induction on addibles
--------------------------------------------------------------------------------
    -- Use case: prove P(i+a) for all addibles a of some number i which lives in
    -- a finite set, by pattern matching on a.
    -- This is not possible in general,
    -- e.g. when trying to define a function 
    --      f : (a : Addibles (fin (ℕ.suc c)) i) → P(i+a)
    -- in case (c : ℕ) and (i : Fin (ℕ.suc c)) are variables that live
    -- in the context and cannot be pattern matched.
    -- FinAddiblesRec allows to define such a function f indirectly using
    -- "Fording" (apparently coined by Connor McBright).
    -- In FinAddiblesRec {ℓ} c i P rec, the function `rec` can be defined via
    -- pattern-matching on a, since in `rec x a` one can first match 
    -- on x to know in which finite set a lives, 
    -- allowing to subsequently match on a.
    FinAddiblesRec
        : {ℓ : Level}
        → (c : ℕ)
        → (i : Fin (ℕ.suc c))
        → (P : Fin (ℕ.suc c) → Set ℓ)
        → ((x : ℕ) → (a : Fin x) → (z : toℕ i Data.Nat.+ x ≡ ℕ.suc c) 
            → P (cast z (i  Data.Fin.+ a)))
        → ((a : Addibles (fin (ℕ.suc c)) i) → P (add (fin (ℕ.suc c)) i a))
    FinAddiblesRec {ℓ} c i P rec a = 
        -- This copies the proof from `add`:
        let meh : toℕ i Data.Nat.≤ ℕ.suc c
            meh = Data.Fin.Properties.toℕ≤n i
        in
        let lemma : toℕ i Data.Nat.+ (ℕ.suc c ∸ toℕ i) ≡ ℕ.suc c
            lemma = Data.Nat.Properties.m+[n∸m]≡n meh
        in
        rec (ℕ.suc c ∸ toℕ i) a lemma
