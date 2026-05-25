-- Module      : Eser.Signature.Splits
-- Description : Combinatorics: num ways to split a number into a sum n = a + b
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- Number of ways to split a number into two positive numbers
-- that sum to the original number.
-- I.e., w ≡ wₐ + wₜ.
-- Use case: Eser.Signature.PiecewiseEnum uses it, with `w` being the weight
-- of a term created with giveArg, `wₜ` being the weight of the base term
-- and `wₐ` being the weight of the argument.
-- The number of ways to construct a term of weight w with n open argument-holes
-- via giveArg is the sum of the number of splits w ↦  (wₐ , wₜ)
-- multiplied with the size of (OpenTerms wₐ 0) × (OpenTerms wₜ (suc n)).

open import Level
open import Data.Bool hiding (_≤_ ; _<_ ; _≤?_)
open import Data.Bool.Properties
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Induction
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Relation.Binary.Structures
open import Data.Fin hiding (_+_ ; _<_ ; _≤_)
open import Data.Vec 
open import Function
open import Relation.Binary.Reasoning.Syntax
open import Data.Fin.Properties using (fromℕ<-toℕ ; toℕ-fromℕ< ; toℕ-injective)

open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)

open import Eser.Equivalences.Notation
open import Eser.Equivalences.Properties
open import Eser.Aux

module Eser.Signature.Splits where

Splits : ℕ → Set
Splits w = Σ[ x ∈ ℕ ] Σ[ y ∈ ℕ ](ℕ.suc x + ℕ.suc y ≡ w)

splitsSize : ℕ → ℕ
splitsSize 0 = 0
splitsSize 1 = 0
splitsSize (suc (suc w)) = ℕ.suc w

-- Given two splits with the same x, the entire splits must be equal.
-- I.e., the first component fixes the rest of the data uniquely as well,
-- at least up to _≡_.
-- (Almost equivalently: for fixed x and w, 
--  the type Σ[ y ∈ ℕ ](ℕ.suc x + ℕ.suc y ≡ w) is proof-irrelevant).
splitsEqLemma
    : (w : ℕ)
    → (s s' : Splits w)
    → proj₁ s ≡ proj₁ s'
    → s ≡ s'
splitsEqLemma w (x , y , p) (x , y' , p') refl =
    let y≡y' : y ≡ y'
        y≡y' = suc-injective  
               $ +-injective {ℕ.suc x} {ℕ.suc y} {ℕ.suc y'} (trans p (sym p'))
    in
    sublemma y≡y' p p'
    where
        sublemma
            : {y y' : ℕ}
            → (y ≡ y')
            → (p : ℕ.suc x + ℕ.suc y ≡ w)
            → (p' : ℕ.suc x + ℕ.suc y' ≡ w)
            → (x , y , p) ≡ (x , y' , p')
        sublemma {y} {y} refl p p' = cong (λ p → (x , y , p)) (≡-irrelevant p p')

-- If (x , y) is a split of w then x < (w-1).
splitsToSmaller
    : (w' : ℕ)
    --→ (x y : ℕ)
    --→ (p : ℕ.suc x + ℕ.suc y ≡ w)
    → (s : Splits (ℕ.suc w'))
    → (proj₁ s < w')
splitsToSmaller w' (x , y , p) 
    = s≤s⁻¹ (≤begin
        ℕ.suc (ℕ.suc x)
        ≤⟨ m≤m+n (ℕ.suc $ ℕ.suc x) y ⟩
        ℕ.suc (ℕ.suc x) + y
        ≤-Reasoning.≡⟨ sym $ +-suc (ℕ.suc x) y ⟩
        ℕ.suc x + ℕ.suc y
        ≤-Reasoning.≡⟨ p ⟩
        ℕ.suc w'
        ≤∎)
        where open ≤-Reasoning renaming (begin_ to ≤begin_ ; _∎ to _≤∎)
splitsFin : (w : ℕ) → Splits w ≃ Fin (splitsSize w)
splitsFin 0 = mk≃' f f⁻¹ invˡ invʳ
    where -- Trivial proof, Agda can already infer both types are empty!
    f : Splits 0 → Fin (splitsSize 0)
    f ()
    f⁻¹ : Fin (splitsSize 0) → Splits 0
    f⁻¹ ()
    invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
    invˡ {()}
    invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
    invʳ {()}
splitsFin 1 = mk≃' f f⁻¹ invˡ invʳ
    where -- 1+x + 1+y ≡ 1 has no solution! But we do need to tell that Agda.
    f : Splits 1 → Fin (splitsSize 1)
    f (x , y , p) = ⊥-elim $ ¬1+m+1+n≡1 p
    f⁻¹ : Fin (splitsSize 1) → Splits 1
    f⁻¹ ()
    invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
    invˡ {()}
    invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
    invʳ {(x , y , p)} = ⊥-elim $ ¬1+m+1+n≡1 p
splitsFin w@(suc w'@(suc w'')) = mk≃' f f⁻¹ invˡ invʳ
    where
    f : Splits w → Fin (splitsSize w)
    f s = fromℕ< (splitsToSmaller w' s)
    f⁻¹ : Fin (splitsSize w) → Splits w
    f⁻¹ x = 
        let -- (y , p) : Σ[ y ∈ Fin (ℕ.suc w) ](toℕ x + toℕ y ≡ w)
            (y , p) = finOppositeSuc w' x
        in
        (toℕ x , toℕ y , p)
    invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
    invˡ {x} {s} refl = 
        ≡begin 
            f s
        ≡⟨⟩ -- Definition f
            fromℕ< (splitsToSmaller w' s)
        ≡⟨ fromℕ<-toℕ x (splitsToSmaller w' s) ⟩
            x
        ≡∎
    invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
    invʳ {s@(x , y , p)} {x'} refl =
        let (x'' , y'' , p'') = f⁻¹ $ f s in
        let H : x'' ≡ x
            H = ≡begin 
                    x''
                ≡⟨⟩
                    (proj₁ $ f⁻¹ $ f s)
                ≡⟨⟩ -- Definition f
                    (proj₁ $ f⁻¹ $ fromℕ< (splitsToSmaller w' s))
                ≡⟨⟩ -- Definition f⁻¹
                    (toℕ $ fromℕ< (splitsToSmaller w' s))
                ≡⟨ toℕ-fromℕ< {x} (splitsToSmaller w' s) ⟩
                    x
                ≡∎
        in
        ≡begin 
            (x'' , y'' , p'')
        ≡⟨ splitsEqLemma w (x'' , y'' , p'') (x , y , p) H ⟩
            (x , y , p)
        ≡∎


split<Left : (m : ℕ) → (s : Splits m) → (ℕ.suc (proj₁ s) < m)
split<Left m s = posSummandsThenSmaller wₜ+wₐ≡m
    where
        wₜ = ℕ.suc (proj₁ s)
        wₐ = ℕ.suc (proj₁ ( proj₂ s))
        wₜ+wₐ≡m = proj₂ (proj₂ s)

split<Right : (m : ℕ) → (s : Splits m) → (ℕ.suc (proj₁ (proj₂ s)) < m)
split<Right m s = posSummandsThenSmaller wₐ+wₜ≡m
    where
        wₜ = ℕ.suc (proj₁ s)
        wₐ = ℕ.suc (proj₁ ( proj₂ s))
        wₜ+wₐ≡m = proj₂ (proj₂ s)
        wₐ+wₜ≡m = subst (λ x → x ≡ m) (+-comm wₜ wₐ) wₜ+wₐ≡m
