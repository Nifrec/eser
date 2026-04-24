-- Module      : Eser.Integers
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
--
-- Implementation note: we define the terms of
-- z ::= 0 | S z | P z
-- both via the `data` keyword (as ℤ')
-- and as the closed terms (as 𝕋) over a signature ℤSig.
-- In principle, we could do all the proofs and correspondences without
-- using the `data` keyword, but this gets thorny because Agda cannot do proper
-- pattern-matching on the elements of ℤ' because it fails to unify 
-- the wₐ + wₜ index in the output of giveArg.
-- This can probably be circumvented by proving that 
-- termCharacterisation
--  : {w : ℕ} 
--  → (t : ClosedTerms ℤSig w) 
--  → (t ≡ O) 
--      ⊎ Σ[ a ∈ ℤ' ] (t ≡ S (proj₂ a))
--      ⊎ Σ[ a ∈ ℤ' ] (t ≡ P (proj₂ a))
-- where:
-- O : ℤ'
-- O = (1 , mk-nullary Fin.zero)

-- S : {w : ℕ} → ClosedTerms {fin 1} {fin 2} ℤSig w → ℤ'
-- S {w} a = (w + 1 , giveArg (mk-multiary Fin.zero) a)

-- P : {w : ℕ} → ClosedTerms {fin 1} {fin 2} ℤSig w → ℤ'
-- P {w} a = (w + 2 , giveArg (mk-multiary $ Fin.suc Fin.zero) a)
--
-- But this approach is less readable and more work
-- than defining the raw terms just via the `data` keyword.

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

module Eser.Examples.Integers where

-- Terms of the grammar z ::= 0 | S z | P z.
data ℤ' : Set where
    O : ℤ'
    S : ℤ' → ℤ'
    P : ℤ' → ℤ'

-- Signature representing the inductive type z ::= 0 | S z | P z.
-- One nullary constructor: 0
-- Two 1-ary constructors: S and P
ℤSig : Signature (fin 1) (fin 2)
ℤSig (Fin.zero) = 0                 -- The arity - 1 of S is 0.
ℤSig (Fin.suc Fin.zero) = 0         -- The arity - 1 of P is 0.

-- Set of all closed terms over ℤSig.
-- It still has different elements, 
-- for example, for `P S 0`, `S P 0` and `0`.
𝕋 : Set
𝕋 = AllTerms {fin 1} {fin 2} ℤSig
--
-- ℤ' is equivalent to the set of all closed terms over ℤSig.
ℤ'≃𝕋 : ℤ' ≃ 𝕋
ℤ'≃𝕋 = ?

ℤenum : ℤ' ≃ ℕ
ℤenum = ≃-trans ℤ'≃𝕋 (infTermAlgEnum {fin 0} {fin 1} ℤSig)

--φ : ℤ' → ℕ
--φ = ≃-to ℤ'enum

--φ⁻¹ : ℕ → ℤ'
--φ⁻¹ = ≃-from ℤ'enum

--φ∘φ⁻¹≈id : (φ ∘ φ⁻¹) ≈ id
--φ∘φ⁻¹≈id = ≃-toFrom ℤ'enum

--φ⁻¹∘φ≈id : (φ⁻¹ ∘ φ) ≈ id
--φ⁻¹∘φ≈id = ≃-fromTo ℤ'enum

open ForEnumSet ℤenum

nf' : ℤ' → ℤ'
nf' O = O
nf' (S O) = S O
nf' (P O) = P O
nf' (S (P t)) = nf' t
nf' (P (S t)) = nf' t
nf' (S (S t)) = S $ S $ nf' t
nf' (P (P t)) = P $ P $ nf' t


nf : ℕ → ℕ
nf = φ ∘ nf' ∘ φ⁻¹ 

-- Proofs that `nf` satisfies the properties of a normal-form function.
nf-leq : NFLeq nf
nf-leq = ?

nf-fix : NFFix nf
nf-fix = ?

-- Actual integers: quotient of ℤ' by the relation encoded in nf.
ℤ : Set
ℤ = ℤenum / (nf , nf-leq , nf-fix)

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

ℤcorrectness : ℤ ≃ StdlibInt.ℤ
ℤcorrectness = ?
