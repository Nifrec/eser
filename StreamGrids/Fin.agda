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
-- Addition in Fin sets
--
-- Theorems about how it behaves with respect to Fin.suc, toℕ and cast.
-- Namely:
-- 1. toℕ (Fin.suc (x F+ y)) ≡ toℕ ( Fin.suc x F+ y)
-- 2. toℕ (x F+ y) ≡ toℕ x ℕ+ toℕ y
--------------------------------------------------------------------------------

_F+_ = Data.Fin._+_
_ℕ+_ = Data.Nat._+_

toℕ-suc-+
    : {c : ℕ}
    → (x y : Fin (ℕ.suc c))
    → toℕ (Fin.suc (x F+ y)) ≡ toℕ ( Fin.suc x F+ y)
toℕ-suc-+ {c} x y = refl -- No idea why refl works, but I'm not complaining!

toℕ-+-comm
    : {c c' : ℕ}
    → (x : Fin (ℕ.suc c))
    → (y : Fin (ℕ.suc c'))
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
    
