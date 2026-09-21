-- Module      : Eser.Sum
-- Description : Extra properties about _/_ and _%_ on ℕ.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
{-# OPTIONS --safe #-}

open import Level hiding (suc)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.DivMod
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Function hiding (_↔_)

open import Eser.Mult using (*-suc')

module Eser.DivMod where

-- #EXT: an easy corollary of this is (m - m%n)/n ≡ m/n.
-- Just rewrite m ≡ [m/n]*n + m%n
-- and use y := [m/n]*n and a := m%n - m%n ≡ 0.
a<n→y≡[y*n+a]/n
    : {a n : ℕ}
    → (y : ℕ)
    → {{_ : NonZero n}}
    → a < n
    → y ≡ (y * n + a) / n
a<n→y≡[y*n+a]/n {a} {suc n'} 0 a<n = 
    sym $ 
    begin 
        (0 * n + a) / n
    ≡⟨ cong (λ x → (x + a) / n) $ *-zeroˡ n ⟩
        a / n
    ≡⟨ m<n⇒m/n≡0 a<n ⟩
        0
    ∎
    where
        n = suc n'
a<n→y≡[y*n+a]/n {a} {suc n'} (suc y) a<n =
    sym $
    begin 
        (1+y * n + a) / n
    ≡⟨ m/n≡1+[m∸n]/n n≤1+y*n+a ⟩
        1 + (1+y * n + a ∸ n) / n
    ≡⟨ cong (λ x → 1 + (x + a ∸ n) / n) $ *-suc' y n ⟩
        1 + (y * n + n + a ∸ n) / n
    ≡⟨ cong (λ x → 1 + (x ∸ n) / n) $ +-assoc (y * n) n a ⟩
        1 + (y * n + (n + a) ∸ n) / n
    ≡⟨ cong (λ x → 1 + (y * n + x ∸ n) / n) $ +-comm n a ⟩
        1 + (y * n + (a + n) ∸ n) / n
    ≡⟨ cong (λ x → 1 + (x ∸ n) / n) $ sym $ +-assoc (y * n) a n ⟩
        1 + (y * n + a + n ∸ n) / n
    ≡⟨ cong (λ x → 1 + x / n) $ m+n∸n≡m (y * n + a) n ⟩
        1 + (y * n + a) / n
    ≡⟨ cong suc (sym $ a<n→y≡[y*n+a]/n {a} {n} y a<n) ⟩
        1 + y
    ≡⟨⟩
        suc y
    ∎
    where
        n = suc n'
        1+y = suc y
        n≤1+y*n : n ≤ 1+y * n
        n≤1+y*n = m≤n*m n 1+y
        n≤1+y*n+a : n ≤ 1+y * n + a
        n≤1+y*n+a = ≤-trans n≤1+y*n (m≤m+n (1+y * n) a)

    


