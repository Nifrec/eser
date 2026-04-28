-- Module      : Eser.Integers.Unused
-- Description : Unused lemmas and definitions for the Integers example
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- Implementing the integers example did not go without hurdles.
-- Here are some working artefacts of those struggles
-- that *might* still be of use in the future.
-- Most likely they won't.
--------------------------------------------------------------------------------

open import Level
open import Data.Bool hiding (_≤_ ; _<_ ; _≤?_)
open import Data.Bool.Properties
open import Data.Nat hiding (_/_)
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

open import Eser.Card
open import Eser.Equivalences.Notation
open import Eser.Equivalences.Properties
open import Eser.Aux
open import Eser.Signature
open import Eser.EqRel
open import Eser.Quotient.Definitions
open import Eser.Signature.NoWeight

module Eser.Examples.Integers where

module NoWeights where

    private
        C : Set
        C = ClosedTermsNW {fin 1} {fin 2} ℤSig

        OT : ℕ → Set
        OT = OpenTermsNW {fin 1} {fin 2} ℤSig
    𝟎 : C
    𝟎 = mk-nullary-nw Fin.zero

    --syntax 𝟎' = 𝟎

    𝐒 : C → C
    𝐒 t = giveArg-nw ( mk-multiary-nw Fin.zero ) t

    𝐏' : C → C
    𝐏' = giveArg-nw $ mk-multiary-nw $ Fin.suc Fin.zero

    syntax 𝐏' t = 𝐏 t

    C≃ℕ : C ≃ ℕ
    C≃ℕ = infTermAlgEnumNW {fin 0} {fin 1} ℤSig

    open ForEnumSet C≃ℕ

    pama-strictly-open
        : (t : OT 1)
        → (t ≡ mk-multiary-nw Fin.zero)
          ⊎ 
          (t ≡ mk-multiary-nw (Fin.suc Fin.zero))
    pama-strictly-open t = ?
        where
            -- Help Agda with inferring underlying base type.
            _≡ₒₜ_ : Rel (Σ[ n ∈ ℕ ] (OT n)) 0ℓ
            x ≡ₒₜ y = _≡_ {A = Σ[ n ∈ ℕ ] (OT n)} x y
            -- Abstract n as a variable, to be able to do pattern-matching.
            sublemma
                : {n : ℕ}
                → (t : OT n)
                → n ≡ 1
                → ((n , t) ≡ₒₜ (1 , mk-multiary-nw Fin.zero))
                  ⊎ 
                  ((n , t) ≡ₒₜ (1 , mk-multiary-nw (Fin.suc Fin.zero)))
            sublemma {n} (mk-multiary-nw Fin.zero) H = {! !}
            sublemma {n} (mk-multiary-nw (Fin.suc c)) H = {! !}
            sublemma {n} (giveArg-nw t a) H = {! !} -- #TODO: derive contradiction

    -- Pattern-matching lemma. We can simulate ℤ' pattern matching.
    -- Just a whole lot more cumbersome.
    pama-lemma
        : (t : C)
        → t ≡ 𝟎 ⊎ Σ[ a ∈ C ] (t ≡ 𝐒 a) ⊎ Σ[ a ∈ C ] (t ≡ 𝐏 a)
    pama-lemma (mk-nullary-nw Fin.zero) = inj₁ refl
    pama-lemma (giveArg-nw t a) with pama-strictly-open t
    ... | inj₁ t≡𝐒 = inj₂ $ inj₁ $ (a , cong (λ t → giveArg-nw t a) t≡𝐒)
    ... | inj₂ t≡𝐏 = inj₂ $ inj₂ $ (a , cong (λ t → giveArg-nw t a) t≡𝐏)

    SinglePaMaCases : (t : C) → Set
    SinglePaMaCases t = t ≡ 𝟎 ⊎ Σ[ a ∈ C ] (t ≡ 𝐒 a) ⊎ Σ[ a ∈ C ] (t ≡ 𝐏 a)

    PaMaCases : (t : C) → Set
    PaMaCases t = t ≡ 𝟎 
                  ⊎ 
                  t ≡ 𝐒 𝟎 
                  ⊎ 
                  t ≡ 𝐏 𝟎 
                  ⊎ 
                  Σ[ a ∈ C ] (t ≡ 𝐒 (𝐒 a)) 
                  ⊎
                  Σ[ a ∈ C ] (t ≡ 𝐒 (𝐏 a)) 
                  ⊎ 
                  Σ[ a ∈ C ] (t ≡ 𝐏 (𝐒 a))
                  ⊎ 
                  Σ[ a ∈ C ] (t ≡ 𝐏 (𝐏 a))
    case1 : {t : C} → t ≡ 𝟎 → PaMaCases t
    case1 = inj₁
    case2 : {t : C} → t ≡ 𝐒 𝟎 → PaMaCases t
    case2 = inj₂ ∘ inj₁
    case3 : {t : C} → t ≡ 𝐏 𝟎 → PaMaCases t
    case3 = inj₂ ∘ inj₂ ∘ inj₁
    case4 : {t : C} → Σ[ a ∈ C ] (t ≡ 𝐒 (𝐒 a)) → PaMaCases t
    case4 = inj₂ ∘ inj₂ ∘ inj₂ ∘ inj₁
    case5 : {t : C} → Σ[ a ∈ C ] (t ≡ 𝐒 (𝐏 a)) → PaMaCases t
    case5 = inj₂ ∘ inj₂ ∘ inj₂ ∘ inj₂ ∘ inj₁
    case6 : {t : C} → Σ[ a ∈ C ] (t ≡ 𝐏 (𝐒 a)) → PaMaCases t
    case6 = inj₂ ∘ inj₂ ∘ inj₂ ∘ inj₂ ∘ inj₂ ∘ inj₁
    case7 : {t : C} → Σ[ a ∈ C ] (t ≡ 𝐏 (𝐏 a)) → PaMaCases t
    case7 = inj₂ ∘ inj₂ ∘ inj₂ ∘ inj₂ ∘ inj₂ ∘ inj₂ 
    --^ Fun fact: case7 is the only one ending in inj₂

    syntax case7 x = inj7 x

    -- Iterating the pama-lemma gives 7 cases
    double-pama-lemma : (t : C) → PaMaCases t
    double-pama-lemma t = sublemma t (pama-lemma t)
        where
            sublemma 
                : (t : C) 
                → t ≡ 𝟎 ⊎ Σ[ a ∈ C ] (t ≡ 𝐒 a) ⊎ Σ[ a ∈ C ] (t ≡ 𝐏 a)
                → PaMaCases t
            sublemmaₛ
                : (t a : C) 
                → t ≡ 𝐒 a
                → a ≡ 𝟎 ⊎ Σ[ a' ∈ C ] (a ≡ 𝐒 a') ⊎ Σ[ a' ∈ C ] (a ≡ 𝐏 a')
                → PaMaCases t
            sublemmaₚ
                : (t a : C) 
                → t ≡ 𝐏 a
                → a ≡ 𝟎 ⊎ Σ[ a' ∈ C ] (a ≡ 𝐒 a') ⊎ Σ[ a' ∈ C ] (a ≡ 𝐏 a')
                → PaMaCases t
            sublemma t (inj₁ refl) = case1 refl
            sublemma t (inj₂ (inj₁ (a , refl))) = sublemmaₛ t a refl (pama-lemma a)
            sublemma t (inj₂ (inj₂ (a , refl))) = sublemmaₚ t a refl (pama-lemma a)
          
            sublemmaₛ t a refl (inj₁ refl) = case2 refl
            sublemmaₛ t a refl (inj₂ (inj₁ (a' , refl))) = case4 (a' , refl)
            sublemmaₛ t a refl (inj₂ (inj₂ (a' , refl))) = case5 (a' , refl)
          
            sublemmaₚ t a refl (inj₁ refl) = case3 refl
            sublemmaₚ t a refl (inj₂ (inj₁ (a' , refl))) = case6 (a' , refl)
            sublemmaₚ t a refl (inj₂ (inj₂ (a' , refl))) = case7 (a' , refl)
