-- Module      : Eser.Equivalences.Properties
-- Description : General theorems about commonly used equivalences
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------

{-# OPTIONS --allow-unsolved-metas #-}

open import Level
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Properties 
    renaming (setoid to mk-≡-setoid)
open import Relation.Nullary
open import Data.Product
open import Relation.Binary.Structures
open import Data.Fin hiding (_+_ ; _<_ ; _≤_)
open import Data.Fin.Properties

open import Function.Related.TypeIsomorphisms
open import Function
open import Function.Properties.Inverse hiding (refl ; trans ; sym)
open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)

open import Eser.Equivalences.Notation

module Eser.Equivalences.Properties where

≃-refl : {A : Set} → (A ≃ A)
≃-refl = ↔-refl

≃-sym : {A B : Set} → (A ≃ B) → (B ≃ A)
≃-sym = ↔-sym

mk≃ = mk↔

mk≃' 
    : {A B : Set}
    → (to : A → B)
    → (from : B → A)
    → (invl : Inverseˡ _≡_ _≡_ to from)
    → (invr : Inverseʳ _≡_ _≡_ to from)
    → A ≃ B
mk≃' {A} {B} to from invl invr = mk↔ (invl , invr)
    
--------------------------------------------------------------------------------
-- Very basic ≃-rewriting theorems
--------------------------------------------------------------------------------


-- If a ≡ a' then B a ≃ B a'.
≃-subst
    : {A : Set}
    → {B : A → Set}
    → {a a' : A}
    → a ≡ a'
    → B a ≃ B a'
≃-subst {A} {B} {a} a≡a' = subst (λ x → B a ≃ B x) a≡a' (≃-refl {B a})


≡-to-≃ 
    : { A A' : Set}
    → A ≡ A'
    → A ≃ A'
≡-to-≃ refl = ≃-refl

--------------------------------------------------------------------------------
-- Rewriting dependent sums Σ
--------------------------------------------------------------------------------


-- If Ba ≃ Ca for all a ∈ A then Σ[a∈A]Ba ≃ Σ[a∈A]Ca.
rewr-≃-under-Σ
    : {A : Set}
    → {B C : A → Set}
    → ((a : A) → (B a ≃ C a))
    → (Σ[ a ∈ A ] B a) ≃ (Σ[ a ∈ A ] C a)
rewr-≃-under-Σ H = ?

--------------------------------------------------------------------------------
-- Rewriting binary sums _⊎_
--------------------------------------------------------------------------------

rewr-≃-under-⊎
    : {A A' B : Set}
    → A ≃ A'
    → (A ⊎ B) ≃ (A' ⊎ B)
rewr-≃-under-⊎ {A} {A'} {B} A≃A' = mk≃' f f⁻¹ invˡ invʳ
    where
        g : A → A'
        g = Inverse.to A≃A'
        g⁻¹ : A' → A
        g⁻¹ = Inverse.from A≃A'
        invˡg : Inverseˡ _≡_ _≡_ g g⁻¹
        invˡg = Inverse.inverseˡ A≃A'
        invʳg : Inverseʳ _≡_ _≡_ g g⁻¹
        invʳg = Inverse.inverseʳ A≃A'

        f : A ⊎ B → A' ⊎ B
        f = Data.Sum.map g id
        f⁻¹ : A' ⊎ B → A ⊎ B
        f⁻¹ = Data.Sum.map g⁻¹ id
        invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
        -- Use that map g h (map g⁻¹ h⁻¹ (inj₁ z)) = inj₁ (g (g⁻¹ (z)))
        -- and then use Inverse.invˡ A≃A'.
        invˡ {inj₁ a'} {y} refl = 
            ≡begin 
                (f $ f⁻¹ $ inj₁ a')
            ≡⟨⟩ -- Definition of Sum.map (functoriality of ⊎): take inj₁ out.
                (inj₁ $ g $ g⁻¹ a')
            ≡⟨ cong inj₁ (invˡg refl) ⟩
                inj₁ a'
            ≡∎
        -- Idem but now for h (which is id in our case)
        invˡ {inj₂ b} {y} refl = 
            ≡begin 
                (f $ f⁻¹ $ inj₂ b)
            ≡⟨⟩
                (inj₂ $ id $ id b)
            ≡⟨⟩
                inj₂ b
            ≡∎
            
        invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
        invʳ {inj₁ a} {y} refl = 
            ≡begin 
                (f⁻¹ $ f $ inj₁ a)
            ≡⟨⟩
                (inj₁ $ g⁻¹ $ g a)
            ≡⟨ cong inj₁ (invʳg refl) ⟩
                inj₁ a
            ≡∎
        invʳ {inj₂ b} {y} refl = 
            ≡begin 
                (f⁻¹ $ f $ inj₂ b)
            ≡⟨⟩
                (inj₂ $ id $ id b)
            ≡⟨⟩
                inj₂ b
            ≡∎

rewr-≃-under-⊎-right
    : {A B B' : Set}
    → B ≃ B'
    → (A ⊎ B) ≃ (A ⊎ B')
rewr-≃-under-⊎-right {A} {B} {B'} B≃B' =
    begin 
        (A ⊎ B)
    ≃⟨ ⊎-comm A B ⟩
        (B ⊎ A)
    ≃⟨ rewr-≃-under-⊎ {B} {B'} {A} B≃B' ⟩
        (B' ⊎ A)
    ≃⟨ ⊎-comm  B' A ⟩
        (A ⊎ B')
    ∎
    
rewr-≃-under-⊎-both
    : {A A' B B' : Set}
    → A ≃ A'
    → B ≃ B'
    → (A ⊎ B) ≃ (A' ⊎ B')
rewr-≃-under-⊎-both {A} {A'} {B} {B'} A≃A' B≃B' =
    begin 
        (A ⊎ B)
    ≃⟨ rewr-≃-under-⊎ A≃A' ⟩
        (A' ⊎ B)
    ≃⟨ rewr-≃-under-⊎-right B≃B' ⟩
        (A' ⊎ B')
    ∎
    
rewr-≃-under-⊎-3
    : {A A' B B' C C' : Set}
    → A ≃ A'
    → B ≃ B'
    → C ≃ C'
    → (A ⊎ B ⊎ C) ≃ (A' ⊎ B' ⊎ C')
rewr-≃-under-⊎-3 {A} {A'} {B} {B'} {C} {C'} A≃A' B≃B' C≃C' =
    let H : (B ⊎ C) ≃ (B' ⊎ C')
        H = rewr-≃-under-⊎-both B≃B' C≃C'
    in
        rewr-≃-under-⊎-both A≃A' H

--------------------------------------------------------------------------------
-- Rewriting expressions involving Fin
--------------------------------------------------------------------------------

fin-+-assoc
    : (n m l : ℕ)
    → Fin (n + (m + l)) ≃ Fin (n + m + l)
fin-+-assoc n m l = 
    let H₁ : (n + (m + l)) ≡ n + m + l
        H₁ = sym (Data.Nat.Properties.+-assoc n m l)
    in
    let H₂ : Fin (n + (m + l)) ≡ Fin (n + m + l)
        H₂ = cong Fin H₁
    in
    ≡-to-≃ H₂

fin-⊎-+
    : (n m : ℕ)
    → ((Fin n) ⊎ (Fin m)) ≃ Fin (n + m)
fin-⊎-+ n m = ≃-sym (Data.Fin.Properties.+↔⊎ {n} {m})

