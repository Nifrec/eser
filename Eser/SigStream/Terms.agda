-- Module      : Eser.SigStream.Terms
-- Description : Two representations of terms in term algebra over a signature.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- Two representations of the term of the term algebra over a signature.
--
-- (1) 𝐕𝐞𝐜𝐓𝐞𝐫𝐦
--  Terms represented by the index of the operation in the signature,
--  and for multiary operations, paired with a vector encoding their arguments,
--  whose length matches their arity.
--  The interpretation is as follows: Vec ℕ m gives the indices of the arguments
--  in an enumeration of all the terms. This interpretation is, of course, 
--  only useful when given an enumeration of all the terms,
--  such that the index assigned to a term is greater than the indices
--  assigned to its arguments.
-- (2) 𝐍𝐞𝐬𝐭𝐞𝐝𝐓𝐞𝐫𝐦
--  Terms represented by the index of the operation in the signature,
--  and for multiary operations, paired with a vector of their ary giving
--  their arguments also as NestedTerms.
--
--  Hence NestedTerms have an inductive structure,
--  whereas VecTerms don't.
--------------------------------------------------------------------------------

open import Level hiding (suc)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Data.Empty
open import Data.Unit
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Data.Vec
open import Data.Vec.Membership.Propositional
open import Data.List renaming (_∷_ to _∷L_) hiding (sum)
open import Function hiding (_↔_)

open import Eser.Signature.Definitions
open import Eser.Card
open import Eser.Equivalences.Notation using (_≃_)

module Eser.SigStream.Terms 
    {μ' ζ' : ℕ∞} 
    (S : Signature (suc∞ μ') (suc∞ ζ')) 
    where

μ = suc∞ μ'
ζ = suc∞ ζ'

ar : cardToSet ζ → ℕ
ar = arity {μ} {ζ} {S = S}

data VecTerm : Set where
    v-nullary : cardToSet μ → VecTerm
    v-muliary : (c : cardToSet ζ) → Vec ℕ (ar c) → VecTerm

data NestedTerm : Set where
    n-nullary : cardToSet μ → NestedTerm
    n-muliary : (c : cardToSet ζ) → Vec NestedTerm (ar c) → NestedTerm

--------------------------------------------------------------------------------
-- Conditional equivalence VecTerm & NestedTerm
--
-- VecTerms and NestedTerms are equivalent given an enumeration
-- of VecTerm that sends terms to greater index than any of its arguments.
--------------------------------------------------------------------------------

IsMultiary : VecTerm → Set
IsMultiary (v-nullary _) = ⊥
IsMultiary (v-muliary _ _) = ⊤

getArity
    : {v : VecTerm}
    → IsMultiary v
    → ℕ
getArity {v-muliary c _} tt = ar c

getVector 
    : {v : VecTerm}
    → (mv : IsMultiary v)
    → Vec ℕ (getArity {v} mv)
getVector {v-muliary _ v} tt = v

MakesArgsSmaller
    : (f : VecTerm → ℕ)
    → Set
MakesArgsSmaller f =
    (c : cardToSet μ)
    → (v : VecTerm)
    → (mv : IsMultiary v)
    → (i : ℕ)
    → (i ∈ (getVector {v} mv))
    → i < f v


theorem-VecTerm-NestedTerm-equiv
    : (e : VecTerm ≃ ℕ)
    → MakesArgsSmaller (Inverse.to e)
    → VecTerm ≃ NestedTerm
theorem-VecTerm-NestedTerm-equiv e H = ?


