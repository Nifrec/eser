-- Module      : Eser.Signature.PiecewiseFin.Definitions
-- Description : Definitions used in PiecewiseFin
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- OT w n = OpenTerms w n
-- In particular, the subtypes of OT w n:
-- OT-Nul w n  ≔ nullary-constructed terms 
-- OT-Mul w n  ≔ multiary-constructed terms, without any argument applied.
-- OT-Arg w n  ≔ multiary-constructed terms, with at least one argument applied.
-- These subtypes correspond to the three constructors of the inductive
-- datatype OpenTerms.

open import Level
open import Data.Bool hiding (_≤_ ; _<_ ; _≤?_)
open import Data.Bool.Properties
open import Data.Nat
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

open import Eser.Aux
open import Eser.Card
open import Eser.Equivalences.Notation
open import Eser.Equivalences.Properties
open import Eser.Signature.Definitions
open import Eser.Signature.Properties
open import Eser.Signature.Splits

module Eser.Signature.PiecewiseFin.Definitions 
    {μ ζ : ℕ∞}
    (S : Signature μ ζ)
    where

ZP  : (w : ℕ) 
    → Set
ZP w = (n : ℕ) → Σ[ z ∈ ℕ ]( OpenTerms {μ} {ζ} S w n ≃ Fin z )

OT = OpenTerms {μ} {ζ} S

IsNullary : {w : ℕ} → {n : ℕ} → OT w n → Set
IsNullary (mk-nullary _) = ⊤
IsNullary (mk-multiary _) = ⊥
IsNullary (giveArg _ _) = ⊥

IsEmptyMultiary : {w : ℕ} → {n : ℕ} → OT w n → Set
IsEmptyMultiary (mk-nullary _) = ⊥
IsEmptyMultiary (mk-multiary _) = ⊤
IsEmptyMultiary (giveArg _ _) = ⊥

IsGiveArg : {w : ℕ} → {n : ℕ} → OT w n → Set
IsGiveArg (mk-nullary _) = ⊥
IsGiveArg (mk-multiary _) = ⊥
IsGiveArg (giveArg _ _) = ⊤

OT-Nul : ℕ → ℕ → Set
OT-Nul w n = Σ[ t ∈ OT w n ] (IsNullary t)

OT-Mul : ℕ → ℕ → Set
OT-Mul w n = Σ[ t ∈ OT w n ] (IsEmptyMultiary t)

OT-Arg : ℕ → ℕ → Set
OT-Arg w n = Σ[ t ∈ OT w n ] (IsGiveArg t)

