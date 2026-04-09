-- Module      : Eser.Signature.Aux
-- Description : Very general (and well-known) definitions and lemmas
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Function

open import Eser.Logic
module Eser.Aux where

--------------------------------------------------------------------------------
-- General mathematical definitions
--------------------------------------------------------------------------------

Between : (a b : ℕ) → ℕ → Set
Between a b ℓ = (a < ℓ) × (ℓ < b)

--------------------------------------------------------------------------------
-- Natural number arithmetic
--------------------------------------------------------------------------------

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

+-injective :
    {n m l : ℕ}
    → n + m ≡ n + l
    → m ≡ l
+-injective {zero} {m} {l} H = H
+-injective {suc n} {m} {l} H = +-injective (suc-injective H)

¬1+m+1+n≡1
    : {m n : ℕ}
    → (ℕ.suc m + ℕ.suc n ≡ 1)
    → ⊥
¬1+m+1+n≡1 {m} {n} p = 
    let H : ℕ.suc ( ℕ.suc (m + n)) ≡ 1
        H = trans (sym $ +-suc (ℕ.suc m) n) p
    in
    1+n≢0 {m + n} (suc-injective H)


bracketRewr : (n m : ℕ) → n + (ℕ.suc $ ℕ.suc m ) ≡ n + 1 + (1 + m)
bracketRewr n m =     
        begin 
            n + (ℕ.suc $ ℕ.suc m )       
        ≡⟨⟩
            n + (1 + ℕ.suc m)
        ≡⟨ sym $ +-assoc n 1 (ℕ.suc m) ⟩
            (n + 1) + ℕ.suc m
        ∎

m<m+1+n : (m n : ℕ) → m < m + (1 + n)
m<m+1+n m n = m<m+n m $ 0<1+n {n}

--------------------------------------------------------------------------------
-- Rewriting equalities
--------------------------------------------------------------------------------
open import Relation.Binary.PropositionalEquality
open import Data.Product

tuple-with-subst
    : {A A' : Set}
    → {B : A' → Set}
    → (f : A → A')
    → (x x' : A)
    → (b : B (f x))
    → x' ≡ x
    → (R : f x ≡ f x')
    → (x' , subst B R b) ≡ (x , b)
tuple-with-subst {A} {A'} {B} f x x b refl refl = refl

--------------------------------------------------------------------------------
-- Finite sets
--------------------------------------------------------------------------------
-- The imports for Fin are down here to avoid name clashes with Data.Nat.
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
            
sucStillSmaller
    : {n m : ℕ}
    → n < m
    → ℕ.suc n ≢ m
    → ℕ.suc n < m
sucStillSmaller {n} {m} n<m 1+n≢m = 
    let 1+n≡m⊎1+n<m : ℕ.suc n < m ⊎ ℕ.suc n ≡ m
        1+n≡m⊎1+n<m = m≤n⇒m<n∨m≡n n<m
    in
    elimCaseRight 1+n≡m⊎1+n<m 1+n≢m

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
    
        

