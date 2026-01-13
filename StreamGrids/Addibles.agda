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
    --Addibles (fin (ℕ.suc c)) n = Fin (ℕ.suc c ∸ toℕ n)
    Addibles (fin (ℕ.suc c)) n = Fin (ℕ.suc (c ∸ toℕ n))

    -- #TODO: Move next theorem to other file.
    -- This theorem exists in Data.Nat.Properties
    -- as `∸-suc`, but my Agda installation fails
    -- to accept any definitions whose name contains `∸`.
    minus-suc : (m n : ℕ) →  m Data.Nat.≤ n → ℕ.suc n ∸ m ≡  ℕ.suc (n ∸ m)
    minus-suc m n z≤n       = refl
    minus-suc (ℕ.suc m) (ℕ.suc n) (s≤s m≤n) = minus-suc m n m≤n

    addablesAreCastable
        : (c : ℕ)
        → (n : Fin (ℕ.suc c))
        → toℕ n Data.Nat.+ (ℕ.suc (c ∸ toℕ n)) ≡ ℕ.suc c
    addablesAreCastable c n = 
        let meh : toℕ n Data.Nat.≤ ℕ.suc c
            meh = Data.Fin.Properties.toℕ≤n n
        in
        let lemma : toℕ n Data.Nat.+ (ℕ.suc c ∸ toℕ n) ≡ ℕ.suc c
            lemma = Data.Nat.Properties.m+[n∸m]≡n meh
        in
        -- Use this:
        let Tn≤Sc : toℕ n Data.Nat.≤ c
            Tn≤Sc = s≤s⁻¹ (toℕ<n n)
        in
        let H : ℕ.suc c ∸ toℕ n ≡ ℕ.suc (c ∸ toℕ n)
            H =  (minus-suc (toℕ n) c Tn≤Sc)
        in
        trans (cong (λ x → toℕ n Data.Nat.+ x) (sym H)) lemma


    -- Add an addible to n while staying in `cardToSet c`.
    add : (c : ℕ∞) → (n : cardToSet c) → Addibles c n → cardToSet c
    add ∞ n m = n Data.Nat.+ m
    add (fin zero) ()
    add (fin (suc c)) n m = cast (addablesAreCastable c n) (n Data.Fin.+ m) 


    addℕzero : (n : ℕ) → add ∞ n ℕ.zero ≡ n
    addℕzero n = Data.Nat.Properties.+-identityʳ n

    addFinZero 
        : (c : ℕ) 
        → (i : Fin (ℕ.suc c))
        → add (fin (ℕ.suc c)) i Fin.zero ≡ i
    addFinZero c Fin.zero = refl
    addFinZero c (Fin.suc i) = 
        let LHS = add (fin (ℕ.suc c)) (Fin.suc i) Fin.zero
        in
        --let check : LHS ≡ 
        ?

    -- Adding the successor of an addible a (if it exists)
    -- is the same as adding a first and then taking the successor of the
    -- output.
    addSucCommℕ
        : (n : ℕ)
        → (a : ℕ)
        → add ∞ n (ℕ.suc a) ≡ ℕ.suc (add ∞ n a)
    addSucCommℕ n m = Data.Nat.Properties.+-suc n m

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
        rec (ℕ.suc (c ∸ toℕ i)) a (addablesAreCastable c i)
