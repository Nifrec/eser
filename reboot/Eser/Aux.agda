-- Module      : Eser.Signature.Aux
-- Description : Very general (and well-known) auxiliary lemmas
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Function

open import Eser.Logic
module Eser.Aux where
-- This is defined in the stdlib, according to the documentation,
-- but for some reason I cannot import it.
∸-suc : {n m : ℕ} → m ≤ n → suc n ∸ m ≡ suc (n ∸ m)
∸-suc z≤n       = refl
∸-suc (s≤s m≤n) = ∸-suc m≤n

m∸Sn≤m∸n
    : (n m : ℕ)
    → m ∸ ℕ.suc n ≤ m ∸ n
m∸Sn≤m∸n n m =
    let H : (m ∸ n) ∸ 1 ≡ m ∸ (ℕ.suc n)
        H = begin 
                (m ∸ n) ∸ 1
            ≡⟨ ∸-+-assoc m n 1 ⟩
                m ∸ (n + 1)
            ≡⟨ cong (λ x → m ∸ x) (+-comm n 1) ⟩
                m ∸ (1 + n)
            ≡⟨⟩
                m ∸ (ℕ.suc n)
            ∎
    in
    subst (λ x → x ≤ m ∸ n) H (m∸n≤m (m ∸ n) 1)
        
sumToSub
    : (m n ℓ : ℕ)
    → m + n ≡ ℓ
    → n ≡ ℓ ∸ m
sumToSub m n ℓ m+n≡ℓ = 
    let H : (m + n) ∸ m ≡ ℓ ∸ m
        H = cong (_∸ m) m+n≡ℓ
    in
    subst (λ x → x ≡ ℓ ∸ m) (Data.Nat.Properties.m+n∸m≡n m n) H

≤⊎< : (n m : ℕ) → n ≤ m ⊎ m < n
≤⊎< n m with n ≤? m
... | yes n≤m = inj₁ n≤m
... | no n≰m = inj₂ (≰⇒> n≰m)

-- If a + b = m and both a≥1 and b≥1 then a<m and b<m.
posSummandsThenSmaller
    : {a b m : ℕ}
    → (ℕ.suc a) + (ℕ.suc b) ≡ m
    → ℕ.suc a < m
posSummandsThenSmaller {a} {b} {m} Sa+Sb≡m =
    let a' = ℕ.suc a
    in
    let H : m ≤ a' ⊎ a' < m
        H = ≤⊎< m a'
    in
    let a+Sb≡Sa+b : a + ℕ.suc b ≡ ℕ.suc a + b
        a+Sb≡Sa+b = +-suc a b
    in
    let a'≤a'+b : a' ≤ a' + b
        a'≤a'+b = m≤n⇒m≤n+o b ≤-refl
    in
    let a'<a'+Sb : a' < a' + ℕ.suc b 
        a'<a'+Sb = s≤s (subst (λ x → a' ≤ x) (sym a+Sb≡Sa+b) a'≤a'+b )
    in
    let m≰a' : ¬ (m ≤ a')
        m≰a' m≤a' = <-irrefl refl 
            (subst (λ x → m < x) Sa+Sb≡m (≤-<-trans m≤a' a'<a'+Sb))
    in
    elimCaseLeft H m≰a'

open import Data.Fin hiding (_≤_ ; _+_ ; _<_)
open import Data.Fin.Properties hiding (_≤?_)
open import Data.Product

finOpposite
    : (w : ℕ)
    → (x : Fin (ℕ.suc w))
    → Σ[ y ∈ Fin (ℕ.suc w) ](toℕ x + toℕ y ≡ w)
finOpposite w x = (opposite x , p)
    where
        y = opposite x
        p =
            begin 
                toℕ x + toℕ y
            ≡⟨ +-comm (toℕ x) (toℕ y) ⟩
                toℕ y + toℕ x
            ≡⟨ cong (λ z → z + toℕ x) (opposite-prop x) ⟩
                ((ℕ.suc w) ∸ (ℕ.suc (toℕ x))) + (toℕ x)
            ≡⟨⟩
                (w ∸ (toℕ x)) + (toℕ x)
            ≡⟨ m∸n+n≡m {w} {toℕ x} (s≤s⁻¹ $ toℕ<n x) ⟩
                w
            ∎
            

-- Given x ∈ Fin (w-1), there exists a y ∈ Fin (w-1)
-- such that 1+x + 1+y ≡ w.
-- Or equivalently, x ∈ Fin w and y ∈ Fin w and 1+x + 1+y ≡ 1+w.
finOppositeSuc
    : (w : ℕ)
    → (x : Fin w)
    → Σ[ y ∈ Fin w ]( ℕ.suc (toℕ x) + ℕ.suc (toℕ y) ≡ ℕ.suc w)
finOppositeSuc 0 ()
finOppositeSuc w@(suc w') x = 
    let (y , x+y≡w') = finOpposite w' x in
    let x' = toℕ x in
    let y' = toℕ y in
    let SS[x+y]≡Sw : ℕ.suc (ℕ.suc (x' + y')) ≡ ℕ.suc w
        SS[x+y]≡Sw = cong (ℕ.suc ∘ ℕ.suc) x+y≡w'
    in
    let p : ℕ.suc (toℕ x) + ℕ.suc (toℕ y) ≡ ℕ.suc w
        p = begin 
                ℕ.suc x' + ℕ.suc y' 
            ≡⟨  +-suc (ℕ.suc x') y'   ⟩
                ℕ.suc (ℕ.suc x') + y'
            ≡⟨⟩ -- Definition of _+_:
                ℕ.suc ( ℕ.suc (x' + y'))
            ≡⟨  SS[x+y]≡Sw ⟩
                ℕ.suc w 
            ∎
    in 
    (y , p)
    
        

