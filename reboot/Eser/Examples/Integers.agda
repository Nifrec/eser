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

--------------------------------------------------------------------------------
-- TODO: move this to another file
--
-- Tools for lifting (properties of) function on A to functions on ℕ.
--------------------------------------------------------------------------------
module EnumLifts {A : Set} (A≃ℕ : A ≃ ℕ) where
    open ForEnumSet A≃ℕ

    elift : (A → A) → ℕ → ℕ
    elift f = φ ∘ f ∘ φ⁻¹

    elift-leq
        : (f : A → A)
        → ((a : A) → f a «= a)
        → ((n : ℕ) → (elift f) n ≤ n)
    elift-leq = ?

    elift-fix
        : (f : A → A)
        → ((a : A) → f (f a) ≡ f a)
        -- → ((n : ℕ) → (elift f $ elift f $ n) ≡ (elift f $ n))
        → ((n : ℕ) → (elift f ( elift f n)) ≡ (elift f n))
    elift-fix = ?



--------------------------------------------------------------------------------
-- NF without inductive type without weights
--------------------------------------------------------------------------------
module NoWeights where

    private
        C : Set
        C = ClosedTermsNW {fin 1} {fin 2} ℤSig

        OT : ℕ → Set
        OT = OpenTermsNW {fin 1} {fin 2} ℤSig

    w : OT 0 → OT 0
    w' : OT 1 → OT 0 → OT 0
    w t@(mk-nullary-nw c) = t
    w (giveArg-nw t' a) = w' t' a
    w' t' a@(mk-nullary-nw c) = giveArg-nw t' a
    w' t' a@(giveArg-nw t'' a') with decEquality {fin 1} {fin 2} ℤSig t' t''
    ... | yes refl = giveArg-nw t' $ w' t'' a'
    ... | no  t'≢t'' = w a'


          
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

ℤ : Set
ℤ = ?

ℤcorrectness : ℤ ≃ StdlibInt.ℤ
ℤcorrectness = ?
