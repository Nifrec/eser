-- Module      : Eser.AltReplacementStructs
-- Description : Sketches for alternative ideas for replacement structures.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------

open import Data.Nat
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Relation.Binary.Definitions using (Decidable ; DecidableEquality)
open import Data.Product
open import Data.Sum
open import Function using (_∘_ ; _$_ ; id)
open import Data.Maybe

module Eser.AltReplacementStructs
    (_⊂_ : ℕ → ℕ → Set)
    (_⊂?_ : Decidable _⊂_)
    where

-- Before the summer holiday, we discussed the following variant.
-- It is the minimal variant of a 'replacement structure'
-- needed to define congruence.
record ReplaceStruct : Set where
    field
        ⊂-resp-< : (y x : ℕ) → x ⊂ y → x < y
        replace : ℕ → ℕ → ℕ → ℕ
        replace-< 
            : (y x x' : ℕ) 
            → x ⊂ y
            → x' < x 
            → (replace y x x' < y)

-- We also decided that we want to show, that the definition
-- for 'Congruence' simplifies to the familiar definition
-- if the underlying ReplaceStruct is a term algebra.
-- Our plan was to do that for my Signatures.
-- But now I am highly uncertain about my Signatures
-- and consider abstracting from the implementation details.

-- The following is still a very coarse abstraction of a term algebra,
-- but with more coherence structure that a ReplaceStruct.
-- One can only replace *all occurrences of an argument at the same time*.
record StrictReplaceStruct : Set where
    field
        ⊂-resp-< : (y x : ℕ) → x ⊂ y → x < y
        replace : ℕ → ℕ → ℕ → ℕ
        replace-< 
            : (y x x' : ℕ) 
            → x ⊂ y
            → x' < x 
            → (replace y x x' < y)
        -- If the argument x is present, then all occurrences of x after
        -- replacing x have dissappeared.
        replace-all-occ
            : (y x x' : ℕ)
            → x ≢ x'
            → ¬ (x ⊂ replace y x x')
        -- If the argument x is present, then replacing x with x'
        -- ensures x' becomes a present argument.
        replace-becomes-occ
            : (y x x' : ℕ)
            → x ⊂ y
            → x' ⊂ replace y x x'
        -- Replacing some argument does not delete the other arguments.
        replace-stability
            : (y x x' z : ℕ)
            → z ≢ x
            → z ⊂ y
            → z ⊂ replace y x x'
        -- Replacing a non-occurrent argument has no effect.
        -- Note: combined with replace-all-occ this implies that `replace`
        -- is idempotent.
        replace-no-effect
            : (y x x' : ℕ)
            → ¬ (x ⊂ y)
            → replace y x x' ≡ y

-- We can also add even more structure, allowing to replace only one specific
-- occurrence of an argument. `I` gives the arities (of the top-level
-- constructor) of each term.
record IndexedReplaceStruct (I : ℕ → Set) 
                            (I-dec : (y : ℕ) → DecidableEquality (I y)) : Set₁
    where
    field
        get : {y : ℕ} → I y → ℕ
        replace : {y : ℕ} → (i : I y) → ℕ → ℕ
        -- Replacing an argument does not change the arity 
        I-stable : {y : ℕ} → (i : I y) → (x : ℕ) → I y ≡ I (replace i x)
        replace-< 
            : {y : ℕ}
            → (i : I y)
            → (x : ℕ)
            → x < get i
            → replace i x < y
        -- Replacing an argument with the same value has no effect:
        replace-≡
            : {y : ℕ}
            → (i : I y)
            → (x : ℕ)
            → x ≡ get i
            → replace i x ≡ y
        replace-get
            : {y : ℕ}
            → (i : I y)
            → (x : ℕ)
            → x ≡ get (subst (λ A → A) (I-stable i x) i)
        replace-stable
            : {y : ℕ}
            → (i j : I y)
            → (x : ℕ)
            → i ≢ j
            → get j ≡ get (subst (λ A → A) (I-stable i x) j)
            
            

