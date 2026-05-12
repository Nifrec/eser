-- Module      : Eser.Examples.Integers
-- Description : Example: constructing type of integers via a quotient.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- This example shows how the type 𝐙 of integers can be constructed by
-- quotienting the inductive type z ::= 0 | S z | P z with a successor- and
-- predecessor-constructor, over the relation (P S z) ~ z ~ (S P z).
-- (i.e., the relation 1 - 1 = 0 = -1 + 1).
--------------------------------------------------------------------------------

open import Level
open import Data.Nat hiding (_/_)
open import Data.Nat.Properties
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Relation.Binary.Structures
open import Function
open import Relation.Binary.Reasoning.Syntax

open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)

open import Eser.Aux using (IsFixpoint)
open import Eser.Equivalences.Notation
open import Eser.Equivalences.Properties
open import Eser.EqRel
open import Eser.Quotient.Definitions

module Eser.Examples.Integers where

open import Eser.Examples.Integers.Definitions public
open import Eser.Examples.Integers.DirectEncProperties public
open import Eser.Examples.Integers.NFLeq public
open import Eser.Examples.Integers.NFFix public

--------------------------------------------------------------------------------
-- Proof that ℤ are indeed the integers
--
-- In particular, we show that our quotient type ℤ is equivalent
-- to the definition of integers used in the standard library.
-- The standard library defines integers as the inductive type
-- with constructors:
--      pos      : ℕ → ℤ
--      negsuc   : ℕ → ℤ
-- with the interpretation that:
--      pos n    = + n
--      negsuc n = - (n+1)
-- (This interpretation avoids having distinct +0 and -0.
--------------------------------------------------------------------------------
open import Data.Integer renaming (ℤ to ℤ#) hiding (_/_)
-- ^ _/_ is already imported from Eser.Quotients.Definitions.

nf-fun : NFFun
nf-fun = (nf , nf-leq , nf-fix)

ℤ : Set
ℤ = ℤ'≃ℕ / nf-fun

--opaque
--    unfolding ℤ'≃ℕ

IsNormal : ℤ' → Set
IsNormal z = IsFixpoint nf (θ z)

-- It holds : (IsClean z) ↔ (nf (ϵ z) ≡ ϵ z)
-- Reason:
-- (1) IsClean z ↔ f z ≡ z
-- (2) nf ≗ elift f
-- and 
-- (3) elift preserves and reflects fixpoints.
normalIfClean : (z : ℤ') → IsClean z → IsNormal z
normalIfClean z p = ?
cleanIfNormal : (z : ℤ') → (nf (θ z) ≡ θ z) → IsClean z
cleanIfNormal z p = ?

abs : (z : ℤ') → IsClean z → ℕ
abs O     p@(inj₁ isZero)       = 0
abs O     p@(inj₂ (inj₁ ()))
abs O     p@(inj₂ (inj₂ ()))
abs (S z) p@(inj₂ (inj₁ isPos)) = ℕ.suc (abs z ?)
abs (P z) p@(inj₂ (inj₂ isNeg)) = ℕ.suc (abs z ?)

χ : ℤ → ℤ#
χ (z , p) = caseDistinction z $ cleanIfNormal z p
    where
        k : IsNormal z
        k = p
        caseDistinction : (z : ℤ') → IsClean z → ℤ#
        caseDistinction O     p@(inj₁ isZero) = + (abs O p) 
        caseDistinction O     p@(inj₂ (inj₁ ()))
        caseDistinction O     p@(inj₂ (inj₂ ()))
        caseDistinction (S z) p@(inj₂ (inj₁ isPos)) = +[1+ abs (S z) p ]
        caseDistinction (P z) p@(inj₂ (inj₂ isNeg)) = -[1+ abs z p' ]
            where
                p' : IsClean z
                p' = is-clean-P-downgrade {z} p
    
-- Make a ℤ' term as a tower of n times `S` applied to O.
S-stack : ℕ → ℤ'
S-stack 0 = O
S-stack (suc n) = S (S-stack n)
P-stack : ℕ → ℤ'
P-stack 0 = O
P-stack (suc n) = P (P-stack n)
S-stack-isPos : (n : ℕ) → IsPos (S-stack $ ℕ.suc n)
S-stack-isPos = ?
P-stack-isNeg : (n : ℕ) → IsNeg (P-stack $ ℕ.suc n)
P-stack-isNeg = ?


β : ℤ# → ℤ
β +0 = (O , normalIfClean O (inj₁ tt))
β +[1+ n ] = (z , (normalIfClean z $ inj₂ $ inj₁ $ S-stack-isPos n))
    where
        z : ℤ'
        z = S-stack (ℕ.suc n)
β -[1+ n ] = (z , (normalIfClean z $ inj₂ $ inj₂ $ P-stack-isNeg n))
    where
        z : ℤ'
        z = P-stack (ℕ.suc n)

ℤcorrectness : ℤ ≃ ℤ#
ℤcorrectness = mk≃' g g⁻¹ invˡ invʳ
    where
    g : ℤ → ℤ#
    g = χ
    g⁻¹ : ℤ# → ℤ
    g⁻¹ = β
    opaque
        invˡ : Inverseˡ _≡_ _≡_ g g⁻¹
        invˡ {x} {y} refl = ?
        invʳ : Inverseʳ _≡_ _≡_ g g⁻¹
        invʳ {y} {x} refl = ?


_ℤ+_ : ℤ → ℤ → ℤ
_ℤ+_ = ?
