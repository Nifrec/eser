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
{-# OPTIONS --allow-unsolved-metas #-}

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
open import StreamGrids.Fin


module StreamGrids.Addibles where

    Addibles : (c : ℕ∞) → (n : cardToSet c) → Set
    Addibles ∞ n = ℕ
    Addibles (fin zero) ()
    --Addibles (fin (ℕ.suc c)) n = Fin (ℕ.suc c ∸ toℕ n)
    Addibles (fin (ℕ.suc c)) n = Fin (ℕ.suc (c ∸ toℕ n))

    -- Add an addible to n while staying in `cardToSet c`.
    add : (c : ℕ∞) → (n : cardToSet c) → Addibles c n → cardToSet c
    add ∞ n m = n Data.Nat.+ m
    add (fin zero) ()
    add (fin (suc c)) n m = cast (castabilityTheorem c n) (n Data.Fin.+ m) 


    addℕzero : (n : ℕ) → add ∞ n ℕ.zero ≡ n
    addℕzero n = Data.Nat.Properties.+-identityʳ n

    ---- #TODO: move to more suitable file.
    ---- 0 Fin.+ n ≐ n holds by definition.
    ---- n Fin.+ 0 ≡ n does not seem to be in the standard library.
    --fin+unital
    --    : {c : ℕ}
    --    → (n : Fin (ℕ.suc c))
    --    → cast (castabilityTheorem c n) (n Data.Fin.+ (Fin.zero {(c ∸ toℕ n)})) ≡ n
    --fin+unital {c} Fin.zero = refl
    --fin+unital {c@(ℕ.suc c')} (Fin.suc n) = 
    --    let casted = (n Data.Fin.+ Fin.zero)
    --    in
    --    let rec = fin+unital {c'} (n) 
    --    in
    --    let H₂ = cong toℕ rec
    --    in
    --    let H₃ = subst (λ x → x ≡ toℕ (n)) (toℕ-cast _ casted) H₂
    --    in
    --    let H₄ : ℕ.suc (toℕ casted) ≡ ℕ.suc (toℕ (n))
    --        H₄ = cong (ℕ.suc) H₃
    --    in
    --    let H₆ : toℕ (Fin.suc casted) ≡ toℕ (cast (castabilityTheorem c' n) (Fin.suc n))
    --        H₆ = subst (λ x → ℕ.suc (toℕ casted) ≡ ℕ.suc x) (toℕ-inject₁ n) H₄
    --    in
    --    ?
    --    ----let H₅ : toℕ (Fin.suc casted) ≡ toℕ (Fin.suc n)
    --    ----    H₅ = subst (λ x → ℕ.suc (toℕ casted) ≡ ℕ.suc x) (toℕ-inject₁ n) H₄
    --    ----in
    --    ----let lemma : 
    --    --let H₆ : Fin.suc casted ≡ Fin.suc n
    --    --    H₆ = toℕ-injective H₄
    --    --in
    --    --{! !}
    ----fin+unital {c} (Fin.suc n) = 
    ----    let casted = (inject₁ n Data.Fin.+ Fin.zero)
    ----    in
    ----    let rec = fin+unital {c} (inject₁ n) 
    ----    in
    ----    let H₂ = cong toℕ rec
    ----    in
    ----    let H₃ = subst (λ x → x ≡ toℕ (inject₁ n)) (toℕ-cast _ casted) H₂
    ----    in
    ----    let H₄ : ℕ.suc (toℕ casted) ≡ ℕ.suc (toℕ (inject₁ n))
    ----        H₄ = cong (ℕ.suc) H₃
    ----    in
    ----    let H₅ : toℕ (Fin.suc casted) ≡ toℕ (Fin.suc n)
    ----        H₅ = subst (λ x → ℕ.suc (toℕ casted) ≡ ℕ.suc x) (toℕ-inject₁ n) H₄
    ----    in
    ----    let H₆ : toℕ (Fin.suc casted) ≡ toℕ (cast (castabilityTheorem c n) (Fin.suc n))
    ----        H₆ = subst (λ x → ℕ.suc (toℕ casted) ≡ ℕ.suc x) (toℕ-inject₁ n) H₄
    ----    in
    ----    let H₆ : Fin.suc casted ≡ Fin.suc n
    ----        H₆ = toℕ-injective H₅
    ----    in
    ----    {! !}

    
        

    addFinZero 
        : (c : ℕ) 
        → (i : Fin (ℕ.suc c))
        → add (fin (ℕ.suc c)) i Fin.zero ≡ i
    addFinZero c Fin.zero = refl
    addFinZero c (Fin.suc i) = 
        let LHS = add (fin (ℕ.suc c)) (Fin.suc i) Fin.zero
        in
        let check : LHS ≡ cast (castabilityTheorem c (Fin.suc i)) ((Fin.suc i) Data.Fin.+ Fin.zero)
            check = refl
        in
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
        rec (ℕ.suc (c ∸ toℕ i)) a (castabilityTheorem c i)
