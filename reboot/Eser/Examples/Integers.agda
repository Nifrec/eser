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

--open import Eser.Card
open import Eser.Equivalences.Notation
open import Eser.Equivalences.Properties
--open import Eser.Aux
--open import Eser.Signature
open import Eser.EqRel
open import Eser.Quotient.Definitions

module Eser.Examples.Integers where

open import Eser.Examples.Integers.Definitions public
--open import Eser.Examples.Integers.DirectEncProperties public
--open import Eser.Examples.Integers.NFLeq public
-- This file runs out of memory:
-- open import Eser.Examples.Integers.NFFix public
-- But it exports just this: 
nf-fix : (n : ℕ) → nf (nf n) ≡ nf n
nf-fix = ?

nf-leq : (n : ℕ) → (nf n) ≤ n
nf-leq = ?

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
import Data.Integer
module StdlibInt = Data.Integer

nf-fun : NFFun
nf-fun = (nf , nf-leq , nf-fix)

ℤ : Set
ℤ = ℤ'≃ℕ / nf-fun

ℤcorrectness : ℤ ≃ StdlibInt.ℤ
ℤcorrectness = mk≃' g g⁻¹ invˡ invʳ
    where
    g : ℤ → StdlibInt.ℤ
    g (O , nf-z-fixpoint) = Data.Integer.+ 0
    g (S z , nf-z-fixpoint) = ?
    g (P z , nf-z-fixpoint) = {! !}
    g⁻¹ : StdlibInt.ℤ → ℤ
    g⁻¹ = ?
    invˡ : Inverseˡ _≡_ _≡_ g g⁻¹
    invˡ {x} {y} refl = ?
    invʳ : Inverseʳ _≡_ _≡_ g g⁻¹
    invʳ {y} {x} refl = ?


_ℤ+_ : ℤ → ℤ → ℤ
_ℤ+_ = ?
