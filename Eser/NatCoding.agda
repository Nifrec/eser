-- Module      : Eser.Signature.NatCoding
-- Description : Encoding and decoding to ℕ of various simple types.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)
open import Data.Vec
open import Data.Vec.Relation.Unary.All
open import Data.Fin using (Fin)
open import Function hiding (_↔_)

open import Eser.Card
open import Eser.Signature
open import Eser.Equivalences.Notation
open import Eser.Equivalences.Properties


module Eser.NatCoding where

code-vec : {n : ℕ} → Vec ℕ (suc n) → ℕ
code-vec {n} v = ?

-- Note: decode-vec uses a different decoding for each length.
-- So one must *explicitly* give the target length as well.
decode-vec : (n : ℕ) → ℕ → Vec ℕ (suc n)
decode-vec n i = ?


Parity : ℕ → Set
Parity n = (Σ[ m ∈ ℕ ] n ≡ m + m) ⊎ (Σ[ m ∈ ℕ ] n ≡ 1 + m + m)
parity' : (n : ℕ) → Parity n
parity' ℕ.zero = inj₁ (0 , refl)
parity' (suc ℕ.zero) = inj₂ (0 , refl) 
parity' (2+ n) = cases (parity' n)
    where
        cases : Parity n → Parity (2+ n)
        cases (inj₁ (m , eq)) = inj₁ (suc m , eq')
            where
                eq' : 2+ n ≡ suc m + suc m
                eq' = 
                    ≡begin 
                        2+ n
                    ≡⟨ cong 2+ eq ⟩
                        2+ (m + m)
                    ≡⟨ cong suc (sym $ +-suc m m) ⟩
                        suc m + suc m
                    ≡∎
        cases (inj₂ (m , eq)) = inj₂ (suc m , eq')
            where
                eq' : 2+ n ≡ 1 + suc m + suc m
                eq' = 
                    ≡begin 
                        2+ n
                    ≡⟨ cong 2+ eq ⟩
                        2+ (1 + m + m)
                    ≡⟨ cong 2+ (sym $ +-suc m m) ⟩
                        2+ m + suc m
                    ≡⟨⟩
                        1 + suc m + suc m
                    ≡∎


-- Encode the left ℕ as the even numbers,
-- and the right ℕ as the odd numbers.
code-sum-fin : ℕ ⊎ ℕ → ℕ
code-sum-fin (inj₁ n) = n + n
code-sum-fin (inj₂ n) = 1 + n + n

decode-sum-fin : ℕ → ℕ ⊎ ℕ
decode-sum-fin n = cases $ parity' n
    where
        cases : Parity n → ℕ ⊎ ℕ
        cases (inj₁ (m , _)) = inj₁ m
        cases (inj₂ (m , _)) = inj₂ m

equiv-sum-fin : (ℕ ⊎ ℕ) ≃ ℕ
equiv-sum-fin = mk≃' f f⁻¹ invˡ invʳ
    where
    f : ℕ ⊎ ℕ → ℕ
    f = code-sum-fin
    f⁻¹ : ℕ → ℕ ⊎ ℕ
    f⁻¹ = decode-sum-fin
    invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
    invˡ {x} {y} refl = ?
    invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
    invʳ {y} {x} refl = ?

decode-vec-lemma
    : {n : ℕ}
    → (i : ℕ)
    → (v : Vec ℕ (suc n))
    → decode-vec n i ≡ v
    → All (_≤ i) v
decode-vec-lemma {n} i v eq = ?

module WithMu (μ' : ℕ∞) where
    μ : ℕ∞
    μ = suc∞ μ'

    code-sum : ^ μ ⊎ ℕ → ℕ
    code-sum = {! code-sum-lemma !}
    decode-sum : ℕ → ^ μ ⊎ ℕ
    decode-sum = {!  !}

    decode-sum-lemma
        : (i w : ℕ)
        → decode-sum i ≡ inj₂ w
        → w < i
    decode-sum-lemma i w eq = ?

module WithZeta (ζ' : ℕ∞) where
    ζ : ℕ∞
    ζ = suc∞ ζ'

    -- #TODO: (de)code pair depends also on ζ
    -- If ^ ζ is finite then there are only finitely many indices.
    -- Need two lemmas: code ℕ × ℕ and code (Fin n) × ℕ.
    code-pair : ^ ζ × ℕ → ℕ
    code-pair = ?
    decode-pair : ℕ → ^ ζ × ℕ 
    decode-pair = ?

    decode-pair-lemma
        : (i y : ℕ)
        → (x : ^ ζ)
        → decode-pair i ≡ (x , y)
        → y ≤ i
    decode-pair-lemma i y x eq = ?




module WithMuZeta (μ' ζ' : ℕ∞) where
    open WithMu μ' public
    open WithZeta ζ' public

    decode-sum-pair-lemma
        : (i w y : ℕ)
        → (x : ^ ζ)
        → decode-sum i ≡ inj₂ w
        → decode-pair w ≡ (x , y)
        → y < i
    decode-sum-pair-lemma i w y x eq-i eq-w = ≤-<-trans y≤w w<i
        where
            y≤w : y ≤ w
            y≤w = decode-pair-lemma w y x eq-w
            w<i : w < i
            w<i = decode-sum-lemma i w eq-i
    
    -- #TODO: move to NewSigStream cuz we have no `ar` here...
