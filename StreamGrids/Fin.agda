-- Module      : StreamGrids.Fin
-- Description : Lemmas about Data.Fin, esp. conversions between fin sets.
-- Copyright   : (c) Lulof Pirée, 2025
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------

---- TODO: probably not all of these are needed.
--open import Data.Bool hiding (_≤_; _≤?_)
--open import Data.Empty
open import Data.Fin hiding (_<_)
open import Data.Fin.Properties
open import Data.Nat
open import Data.Nat.Properties
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding ([_])
open ≡-Reasoning

module StreamGrids.Fin where

-- toℕ commutes with suc (although it swaps Fin.suc with Nat.suc, of course).
toℕ-suc
    : {c : ℕ}
    → (n : Fin c)
    → toℕ (Fin.suc n) ≡ ℕ.suc (toℕ n)
toℕ-suc {c} n = toℕ-↑ʳ 1 n

lower-s≤s
    : {c k : ℕ}
    → (n : Fin c)
    → (h : toℕ n Data.Nat.< k)
    → Fin.suc (lower n h) ≡ lower (Fin.suc n) (s≤s h)
lower-s≤s {suc c} zero (s≤s z≤n) = refl
lower-s≤s {suc c} (suc n) (s≤s h) = refl

-- #TODO: all the let-ins are superfluous, the proofs can be directly
-- written inside the ⟨...⟩s.
-- I used the let-ins to typecheck ideas step-by-step.
toℕ-lower
    : {c k : ℕ}
    → (n : Fin c)
    → (h : toℕ n Data.Nat.< k)
    → toℕ (lower n h) ≡ toℕ n
toℕ-lower {suc c} {suc k'} zero (s≤s z≤n) = refl
toℕ-lower {c@(suc c')} {k@(suc k')} (suc n) h@(s≤s h') = 
    let TLn≡Tn : toℕ (lower n h') ≡ toℕ n
        TLn≡Tn = toℕ-lower {c'} {k'} n h'
    in
    let STLn≡STn : suc (toℕ (lower n h')) ≡ suc (toℕ n)
        STLn≡STn = cong suc TLn≡Tn
    in
    let STn≡STn : suc (toℕ n) ≡ toℕ (Fin.suc n)
        STn≡STn = toℕ-suc n
    in
    let STLn≡TSLn : suc (toℕ (lower n h')) ≡ toℕ (Fin.suc (lower n h'))
        STLn≡TSLn = toℕ-suc (lower n h')
    in
    let TSLn≡TLSn : toℕ (Fin.suc (lower n h')) ≡ toℕ (lower (suc n) h)
        TSLn≡TLSn = cong toℕ (lower-s≤s n h')
    in
    sym(
    begin
        toℕ (suc n) 
        ≡⟨ toℕ-suc n ⟩
        suc (toℕ n)
        ≡⟨ sym STLn≡STn ⟩
        suc (toℕ (lower n h'))
        ≡⟨ STLn≡TSLn ⟩
        toℕ (Fin.suc (lower n h'))
        ≡⟨ TSLn≡TLSn ⟩
        toℕ (lower (suc n) h)
    ∎)

--------------------------------------------------------------------------------
-- Addition in Finite sets
--
-- Theorems about how it behaves with respect to Fin.suc, toℕ and cast.
-- Namely:
-- 1. toℕ (Fin.suc (x F+ y)) ≡ toℕ ( Fin.suc x F+ y)
--      (this actually holds already definitionally, in hindsight)
-- 2. toℕ (x F+ y) ≡ toℕ x ℕ+ toℕ y
-- 3. Fin.suc (cast z (x F+ y)) ≡ cast Sz (Fin.suc x F+ y)
-- 4. toℕ n ℕ+ (ℕ.suc (c ∸ toℕ n)) ≡ ℕ.suc c
--  (this gives a sufficient condition for a cast to be possible: 
--  if `n : Fin (ℕ.suc c)` and `m : Fin (ℕ.suc (c ∸ toℕ n))` 
--  then one can cast `n F+ m` back into n's original type `Fin (ℕ.suc c)`).
-- 5. i ≡ cast z (i F+ (Fin.zero {c ∸ toℕ i}))
--------------------------------------------------------------------------------

_F+_ = Data.Fin._+_
_ℕ+_ = Data.Nat._+_

toℕ-suc-+
    : {c : ℕ}
    → (x y : Fin (ℕ.suc c))
    → toℕ (Fin.suc (x F+ y)) ≡ toℕ ( Fin.suc x F+ y)
-- This holds by definition because of the recursive definition of + in Fin:
--      (Fin.suc x) + y ≐ Fin.suc (x + y)
toℕ-suc-+ {c} x y = refl 

toℕ-+-comm
    : {c k : ℕ}
    → (x : Fin c)
    → (y : Fin k)
    → toℕ (x F+ y) ≡ toℕ x ℕ+ toℕ y
toℕ-+-comm {c} zero zero = refl
toℕ-+-comm {c} zero (suc y) = refl
toℕ-+-comm {ℕ.suc c} (suc x) y =
    sym (
    begin 
    toℕ (suc x) ℕ+ toℕ y
    ≡⟨ refl ⟩
    ℕ.suc (toℕ x ℕ+ toℕ y)
    ≡⟨ cong ℕ.suc (sym (toℕ-+-comm x y)) ⟩
    ℕ.suc (toℕ (x F+ y))
    ≡⟨ refl ⟩
    toℕ (suc x F+ y)
    ∎
    )
    
cast-suc-comm
    : {c k : ℕ}
    → (x : Fin (ℕ.suc c))
    → (y : Fin k)
    → (z : toℕ x ℕ+ k ≡ ℕ.suc c)
    -- #TODO: the existence of Sz is implied by z, and this type is proof
    -- irrelevant anyway, so the argument Sz is superfluous.
    → (Sz : toℕ (Fin.suc x) ℕ+ k ≡ ℕ.suc (ℕ.suc c))
    → Fin.suc (cast z (x F+ y)) ≡ cast Sz (Fin.suc x F+ y)
cast-suc-comm x y z Sz = 
    let lemma : toℕ( Fin.suc (cast z (x F+ y))) ≡ toℕ( cast Sz (Fin.suc x F+ y))
        lemma = begin 
                toℕ( Fin.suc (cast z (x F+ y)))
                ≡⟨ refl ⟩
                ℕ.suc (toℕ( cast z (x F+ y)))
                ≡⟨ cong ℕ.suc (toℕ-cast z (x F+ y)) ⟩
                ℕ.suc (toℕ( x F+ y ))
                ≡⟨ cong ℕ.suc (toℕ-+-comm x y)  ⟩
                ℕ.suc (toℕ x ℕ+ toℕ y)
                ≡⟨ refl ⟩ -- Definition of ℕ+ backward.
                ℕ.suc (toℕ x)  ℕ+ toℕ y
                ≡⟨ refl ⟩
                toℕ (Fin.suc x) ℕ+ toℕ y
                ≡⟨ sym (toℕ-+-comm (Fin.suc x) y)  ⟩
                toℕ (Fin.suc x F+ y)
                ≡⟨ sym (toℕ-cast Sz (Fin.suc x F+ y)) ⟩
                toℕ( cast Sz (Fin.suc x F+ y))
                ∎
    in
    toℕ-injective lemma

-- This lemma exists in Data.Nat.Properties
-- as `∸-suc`, but my Agda installation fails
-- to accept any definitions whose name contains `∸`.
minus-suc : (m n : ℕ) →  m Data.Nat.≤ n → ℕ.suc n ∸ m ≡  ℕ.suc (n ∸ m)
minus-suc m n z≤n       = refl
minus-suc (ℕ.suc m) (ℕ.suc n) (s≤s m≤n) = minus-suc m n m≤n


-- Useful to know: if given `n : Fin (ℕ.suc c)`,
-- then one can add any `m : Fin (ℕ.suc (c ∸ toℕ n))`
-- while staying in `Fin (ℕ.suc c)`, in the sense that
-- `n F+ m : Fin (toℕ n + ℕ.suc (c ∸ toℕ n))`,
-- but that type is ≡ to `Fin (ℕ.suc c)`,
-- so one has 
--      `cast (castabilityTheorem c n) (n F+ m) : Fin (ℕ.suc c)`,
--      i.e., add something to `n` while staying *within* `Fin (ℕ.suc c)`.
-- (Note: (ℕ.suc c) ∸ toℕ n ≡ ℕ.suc (c ∸ toℕ n)`,
-- but the RHS makes Agda see at type level that a finite set with that
-- cardinality has at least the element Fin.zero, which can sometimes be
-- convenient.)
castabilityTheorem
    : (c : ℕ)
    → (n : Fin (ℕ.suc c))
    → toℕ n ℕ+ (ℕ.suc (c ∸ toℕ n)) ≡ ℕ.suc c
castabilityTheorem c n = 
    let meh : toℕ n Data.Nat.≤ ℕ.suc c
        meh = Data.Fin.Properties.toℕ≤n n
    in
    let lemma : toℕ n Data.Nat.+ (ℕ.suc c ∸ toℕ n) ≡ ℕ.suc c
        lemma = Data.Nat.Properties.m+[n∸m]≡n meh
    in
    let Tn≤Sc : toℕ n Data.Nat.≤ c
        Tn≤Sc = s≤s⁻¹ (toℕ<n n)
    in
    let H : ℕ.suc c ∸ toℕ n ≡ ℕ.suc (c ∸ toℕ n)
        H =  (minus-suc (toℕ n) c Tn≤Sc)
    in
    trans (cong (λ x → toℕ n Data.Nat.+ x) (sym H)) lemma


-- The closest thing one can show in Fin to "i + 0 ≡ i".
addFinZeroCasted
    : (c x : ℕ) 
    → (i : Fin (ℕ.suc c))
    → (z : toℕ i ℕ+ ℕ.suc x ≡ ℕ.suc c)
    → i ≡ cast z (i F+ (Fin.zero {x}))
addFinZeroCasted c x Fin.zero refl = refl
addFinZeroCasted (ℕ.suc c) (x) (Fin.suc i) z = 
    let z1 : toℕ i ℕ+ (ℕ.suc (x)) ≡ ℕ.suc c
        z1 = Data.Nat.Properties.suc-injective z
    in
    let H₁ : i ≡ cast z1 (i F+ (Fin.zero {x}))
        H₁ = addFinZeroCasted c (x) i z1
    in
    let H₂ : Fin.suc i ≡ Fin.suc (cast z1 (i F+ Fin.zero))
        H₂ = cong Fin.suc H₁
    in
    let H₃ : Fin.suc i ≡ (cast z (Fin.suc i F+ Fin.zero))
        H₃ = trans H₂ (cast-suc-comm i Fin.zero z1 z)
    in
    H₃

-- Alternative theorem stating i + 0 ≡ i,
-- using a canonical proof of castability to the same finite set.
-- ('Canonical' means via the castabilityTheorem).
addFinZeroCastedCanonical
    : (c : ℕ) 
    → (i : Fin (ℕ.suc c))
    → i ≡ cast (castabilityTheorem c i) (i F+ (Fin.zero {c ∸ toℕ i}))
addFinZeroCastedCanonical c Fin.zero = refl
addFinZeroCastedCanonical (ℕ.suc c) (Fin.suc i) = 
    let z1 : toℕ i ℕ+ ℕ.suc (c ∸ toℕ i) ≡ ℕ.suc c
        z1 = castabilityTheorem c i
    in
    let z = castabilityTheorem (ℕ.suc c) (Fin.suc i)
    in
    let H₁ : i ≡ cast z1 (i F+ Fin.zero)
        H₁ = addFinZeroCastedCanonical c i
    in
    let H₂ : Fin.suc i ≡ Fin.suc (cast z1 (i F+ Fin.zero))
        H₂ = cong Fin.suc H₁
    in
    let H₃ : Fin.suc i ≡ (cast z (Fin.suc i F+ Fin.zero))
        H₃ = trans H₂ (cast-suc-comm i Fin.zero z1 z)
    in
    H₃
