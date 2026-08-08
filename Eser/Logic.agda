-- Module      : Eser.Logic
-- Description : Basic logic auxiliary functions
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------

module Eser.Logic where

open import Data.Sum
open import Relation.Nullary
open import Data.Empty
open import Data.Bool
open import Relation.Binary.Definitions using (DecidableEquality)
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Function using (_$_)

-- This also works with `¬ (A ⊎ B)`, as it is a shorthand for `A ⊎ B → ⊥` 
-- (i.e., special case with `C := ⊥`).
orWeakenLeft : {A B C : Set} → (A ⊎ B → C) → A → C
orWeakenLeft p = λ a → p (inj₁ a)
orWeakenRight : {A B C : Set} → (A ⊎ B → C) → B → C
orWeakenRight p = λ b → p (inj₂ b)

elimCaseLeft : {A B : Set} → (A ⊎ B) → (¬ A) → B
elimCaseLeft (inj₁ a) ¬A = ⊥-elim (¬A a)
elimCaseLeft (inj₂ b) = λ _ → b
elimCaseRight : {A B : Set} → (A ⊎ B) → (¬ B) → A
elimCaseRight (inj₁ a) = λ _ → a
elimCaseRight (inj₂ b) ¬B = ⊥-elim (¬B b)

-- If X⊎Y and X→Z then Z⊎Y.
implCongrLeft
    : {X Y Z : Set}
    → X ⊎ Y
    → (X → Z)
    → Z ⊎ Y
implCongrLeft (inj₁ x) f = inj₁ (f x)
implCongrLeft (inj₂ y) f = inj₂ y

implCongrRight
    : {X Y Z : Set}
    → X ⊎ Y
    → (Y → Z)
    → X ⊎ Z
implCongrRight (inj₁ x) f = inj₁ x
implCongrRight (inj₂ y) f = inj₂ (f y)

--------------------------------------------------------------------------------
-- Logic on terms of Data.Bool (instead of on types-as-propositions)
--------------------------------------------------------------------------------

true≢false : true ≢ false
true≢false ()

-- If A ∧ B is true then both A and B are true.
∧-elim-left
    : (a b : Bool)
    → a ∧ b ≡ true
    → a ≡ true
∧-elim-left true true refl = refl
∧-elim-right
    : (a b : Bool)
    → a ∧ b ≡ true
    → b ≡ true
∧-elim-right true true refl = refl

-- If A => B then A ∧ B is equal to A.
∧-left-implies-right
    : (a b : Bool)
    → (a ≡ true → b ≡ true)
    → a ∧ b ≡ a
∧-left-implies-right false b a=>b = refl
∧-left-implies-right true b a=>b = 
    begin 
        true ∧ b
    ≡⟨ cong (true ∧_) (a=>b refl) ⟩
        true ∧ true
    ≡⟨⟩
        true
    ∎


--------------------------------------------------------------------------------
-- Extracting proofs from decidable equivalence relations.
-- And vice versa.
--------------------------------------------------------------------------------

decEqReflection
    : {A : Set}
    → (_≡?_ : DecidableEquality A)
    → (a b : A)
    → does (a ≡? b) ≡ true
    → a ≡ b
decEqReflection {A} _≡?_ a b p = q'
    where
        q : Reflects (a ≡ b) (does (a ≡? b))
        q = proof (a ≡? b)
        q' : a ≡ b
        q' = invert ( (subst (λ x → Reflects (a ≡ b) x) p q))

-- Given a proof of truth, force the Bool-part of a decidable type to be `true`.
-- (This might exist in the StdLib, but I could not find it).
forceDoesTrue
    : {A : Set}
    → (d : Dec A)
    → A
    → does d ≡ true
forceDoesTrue {A} (no ¬a) a = ⊥-elim $ ¬a a
forceDoesTrue {A} (yes a) _ = refl

decEqCoReflection
    : {A : Set}
    → (_≡?_ : DecidableEquality A)
    → (a b : A)
    → a ≡ b
    → does (a ≡? b) ≡ true
decEqCoReflection {A} _≡?_ a a refl 
    = decEqCoReflectionCases _≡?_ a a refl (does (a ≡? a)) refl
    where
        decEqCoReflectionCases
            : {A : Set}
            → (_≡?_ : DecidableEquality A)
            → (a b : A)
            → a ≡ b
            → (x : Bool)
            → (x ≡ does (a ≡? b))
            → x ≡ true
        decEqCoReflectionCases _≡?_ a a refl false p = 
            ⊥-elim $ true≢false $ sym $ 
                subst (λ z → false ≡ z) (forceDoesTrue {a ≡ a} (a ≡? a) refl) p
        decEqCoReflectionCases _≡?_ a a refl true p = refl

--------------------------------------------------------------------------------
-- Conversions between ≡ᵇ and ≡ in ℕ. 
--------------------------------------------------------------------------------
module _ where
    open import Data.Nat

    ≡→≡ᵇ
        : (m n : ℕ)
        → m ≡ n
        → (m ≡ᵇ n) ≡ true
    ≡→≡ᵇ zero zero refl = refl
    ≡→≡ᵇ (suc m) (suc m) refl = ≡→≡ᵇ m m refl

    ≡ᵇ→≡
        : (m n : ℕ)
        → (m ≡ᵇ n) ≡ true
        → m ≡ n
    ≡ᵇ→≡ 0 0 refl = refl
    ≡ᵇ→≡ (suc m) (suc n) p = cong suc (≡ᵇ→≡ m n p)

