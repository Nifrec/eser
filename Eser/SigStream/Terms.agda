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
-- We want the 'here' of _∈_ not of _[_]=_.
open import Data.Vec hiding (here ; there) 
open import Data.Vec.Membership.Propositional
open import Data.Vec.Relation.Unary.Any
open import Data.List renaming (_∷_ to _∷L_) hiding (sum ; length)
open import Function hiding (_↔_)

open import Eser.Signature.Definitions
open import Eser.Card
open import Eser.Equivalences.Notation using (_≃_)
open import Eser.Equivalences.Properties using (mk≃')

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
    v-multiary : (c : cardToSet ζ) → Vec ℕ (ar c) → VecTerm

data NestedTerm : Set where
    n-nullary : cardToSet μ → NestedTerm
    n-multiary : (c : cardToSet ζ) → Vec NestedTerm (ar c) → NestedTerm

max : {n : ℕ} → Vec ℕ (suc n) → ℕ
max {0} (x ∷ []) = x
max {suc n} (x ∷ xs) = cases (x <? (max xs))
    where
        cases : (Dec (x < (max xs))) → ℕ
        cases (yes _) = max xs
        cases (no _)  = x

height : NestedTerm → ℕ
height (n-nullary _) = 0
height (n-multiary _ v) = suc $ max $ Data.Vec.map height v
--------------------------------------------------------------------------------
-- Conditional equivalence VecTerm & NestedTerm
--
-- VecTerms and NestedTerms are equivalent given an enumeration
-- of VecTerm that sends terms to greater index than any of its arguments.
--------------------------------------------------------------------------------

IsMultiary : VecTerm → Set
IsMultiary (v-nullary _) = ⊥
IsMultiary (v-multiary _ _) = ⊤

getArity
    : {v : VecTerm}
    → IsMultiary v
    → ℕ
getArity {v-multiary c _} tt = ar c

getVector 
    : {v : VecTerm}
    → (mv : IsMultiary v)
    → Vec ℕ (getArity {v} mv)
getVector {v-multiary _ v} tt = v

MakesArgsSmaller
    : (f : VecTerm → ℕ)
    → Set
MakesArgsSmaller f =
      (v : VecTerm)
    → (mv : IsMultiary v)
    → (i : ℕ)
    → (i ∈ (getVector {v} mv))
    → i < f v


--theorem-VecTerm-NestedTerm-equiv
--    : (e : VecTerm ≃ ℕ)
--    → MakesArgsSmaller (Inverse.to e)
--    → VecTerm ≃ NestedTerm
--theorem-VecTerm-NestedTerm-equiv e H = ?

theorem-ℕ-NestedTerm-equiv
    : (e : VecTerm ≃ ℕ)
    → MakesArgsSmaller (Inverse.to e)
    → ℕ ≃ NestedTerm
theorem-ℕ-NestedTerm-equiv e H = mk≃' g f invˡ invʳ
    where
    -- Fuel technique is used, variable b gives the fuel.
    -- This is to make Agda's termination checker happy.
    -- g' only accepts inputs in ℕ smaller than the fuel.
    -- f' only accepts NestedTerms whose height is smaller than the fuel.

    open Eser.Equivalences.Notation.EquivShorthands e

    g' : (b n : ℕ) → n < b → NestedTerm
    g' b 0 0<b = cases (φ⁻¹ 0) refl
        where
            cases : (x : VecTerm) → (x ≡ φ⁻¹ 0) → NestedTerm
            cases (v-nullary c) _ = n-nullary c
            -- This case is impossible;
            -- no multiary term can be the φ⁻¹-image of 0.
            cases x@(v-multiary c (i ∷ is)) p = ⊥-elim $ n≮0 i<0
                where
                    i<φt : i < φ x
                    i<φt = H x tt i (Any.here {x = i} {xs = is} refl)

                    eq : φ x ≡ 0
                    eq = begin 
                            φ x
                        ≡⟨ cong φ p ⟩
                            φ (φ⁻¹ 0)
                        ≡⟨ φ∘φ⁻¹≈id 0 ⟩
                            0
                        ∎

                    i<0 : i < 0
                    i<0 = subst (i <_) eq i<φt
                    
    g' (suc b) (suc n) 1+n<1+b@(s≤s n<b) = cases (φ⁻¹ (suc n)) refl
        where
            cases : (x : VecTerm) → (x ≡ φ⁻¹ (suc n)) → NestedTerm
            cases (v-nullary c) _ = n-nullary c
            cases x@(v-multiary c v) p = n-multiary c v'
                where
                    eq : φ x ≡ suc n
                    eq = begin 
                            φ x
                        ≡⟨ cong φ p ⟩
                            φ (φ⁻¹ (suc n))
                        ≡⟨ φ∘φ⁻¹≈id (suc n) ⟩
                            suc n
                        ∎
                    fun : {i : ℕ} → i ∈ v → NestedTerm
                    fun {i} i∈v = g' b i i<b
                        where
                            i<b : i < b
                            i<b = s≤s⁻¹ $ ≤-<-trans 
                                    (subst (i <_) eq (H x tt i i∈v)) 
                                    1+n<1+b
                    v' : Vec NestedTerm (length v)
                    v' = mapWith∈ v fun
    g : ℕ → NestedTerm
    g n = g' (suc n) n (n<1+n n)

    f' : (b : ℕ) → (t : NestedTerm) → (height t < b) → ℕ
    f' b t p = ?

    f : NestedTerm → ℕ
    f t = f' (suc (height t)) t (n<1+n $ height t)

    invˡ : Inverseˡ _≡_ _≡_ g f
    invˡ {x} {y} refl = ?
    invʳ : Inverseʳ _≡_ _≡_ g f
    invʳ {y} {x} refl = ?


