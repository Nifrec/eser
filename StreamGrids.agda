-- Module      : StreamGrids
-- Description : Coinductive representation of grids
-- Copyright   : (c) Lulof Pirée, 2025
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- 
-- Main file exporting all related definitions.

module StreamGrids where

-- TODO: probably not all of these are needed.
open import Data.Bool hiding (_≤_; _≤?_)
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Fin
open import Data.Sum
open import Data.Unit
open import Level using (0ℓ)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

-- An alphabet is an ordered collection of atomic symbols.
-- Currently it just wraps `Fin`, but this wrapper allows to change
-- the representation of alphabets if needed later
-- (e.g., I also consider 
-- Alphabet : Set → Set
-- Alphabet A = List A
-- )
--Alphabet : Set
--Alphabet = Σ[ n ∈ ℕ ] (Fin n)
--data Alphabet : Set where
--    fsetAlphabet : ℕ → Alphabet

Alphabet : ℕ → Set
Alphabet n = Fin (suc n)


--_atom-<_ : {A : Set} → (Alphabet A) → Rel 0ℓ (Alphabet A)
--_atom-<_ = 

open import Data.List.Relation.Binary.Lex
lexleq : (n : ℕ) → Rel (List (Fin (suc n))) 0ℓ
-- Fin n is the underlying type.
-- ⊤ means that the empty list is related to itself.
-- _≣_ is for equality between elements.
--lexleq n = Lex-≤ {Fin (suc n)} (⊤) (_≡_) (Data.Fin._<_)
lexleq n = Lex-≤ (_≡_) (Data.Fin._<_)

-- The list [2, 1, 0]
α : List (Fin 3)
α =  Fin.suc (Fin.suc Fin.zero) ∷ Fin.suc (Fin.zero) ∷ Fin.zero ∷ []
-- The list [1, 2, 2]
β : List (Fin 3)
β = Fin.suc (Fin.zero) ∷ Fin.suc (Fin.suc Fin.zero) ∷ 
    Fin.suc (Fin.suc Fin.zero) ∷ []

check : lexleq 2 α β
check = this (s≤s {! (n≮0 2) !})
