-- Module      : Eser.Signatures
-- Description : Tools for enumerating term algebras over signatures
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
open import Level
open import Data.Bool hiding (_≤_ ; _<_ ; _≤?_)
open import Data.Bool.Properties using (¬-not ; not-¬)
open import Data.Nat
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Data.Product
--open import Relation.Binary.Structures
open import Data.Fin hiding (_≤_ ; _≤?_)
open import Data.List
open import Data.Vec hiding (restrict)
--open import Data.Nat.Properties using (≤-refl ; ≤-trans ; ≤-<-trans ; n≤0⇒n≡0 
--                                       ; n≤1+n ; m≤n⇒m<n∨m≡n ; _≤?_ ; ≰⇒≥)
--open import Data.Fin.Properties using (toℕ<n)
--open import Relation.Nullary -- Needed for with-abstractions on decidable ≡.
--open import Function hiding (_↔_)

--open import Eser.Logic using (elimCaseLeft ; elimCaseRight)
--open import Relation.Nullary
--open ≡-Reasoning
--open import Data.Nat.Properties
--open import Data.Fin
--open import Data.Fin.Properties
--open import Data.Fin.Induction
--open import Data.Empty
--open import Data.List
--open import Data.List.Relation.Unary.AllPairs using (AllPairs)
--open import Data.List.Relation.Unary.All using (All)
--open import Data.List.Relation.Binary.Suffix.Heterogeneous using (Suffix)
--open import Data.List.Membership.Propositional using (_∈_ ; _∉_ )
--open import Data.List.Membership.Propositional.Properties using (∈-lookup)
--open import Data.List.Relation.Unary.Any using (Any)

--open import Eser.Definitions using (_≈_)

module Eser.Signatures where


---- Very terse representation of signatures,
---- parametrised by a type `N` of constructor names
---- (e.g., use N ≔ String).
---- Constructors either have arity 0 or suc a.
---- Constructors either take one external argument from ℕ,
---- or no recursive arguments.
--record TerseSignature (N : Set) : Set where
--    record
--        pure-nullary : [ N ]
--        ℕ-nullary    : [ N ]
--        pure-multiary : [ N × ℕ ]
--        ℕ-multiary : [ N × ℕ ]


-- Very terse representation of signatures.
-- Constructors either have arity 0 or suc a.
-- Constructors either take one external argument from ℕ,
-- or no recursive arguments.
record TerseSignature : Set where
   field 
        pure-nullary : ℕ
        ℕ-nullary    : ℕ
        pure-multiary : List ℕ
        ℕ-multiary : List ℕ
open TerseSignature

indices : {A : Set} → List A → Set
indices {A} L = Fin (Data.List.length L)
 
-- Term algebra over a TerseSignature.
data TerseFreeTerm (S : TerseSignature) : Set where
    mk-pure-nullary : Fin (pure-nullary S) → TerseFreeTerm S
    mk-ℕ-nullary : Fin (ℕ-nullary S) → ℕ → TerseFreeTerm S
    mk-pure-multiary 
        : (c : indices (pure-multiary S)) 
        → (Vec (TerseFreeTerm S) (Data.List.lookup (pure-multiary S) c)) 
        → TerseFreeTerm S 
    mk-ℕ-multiary 
        : (c : indices (pure-multiary S)) 
        → (Vec (TerseFreeTerm S) (Data.List.lookup (pure-multiary S) c)) 
        → ℕ
        → TerseFreeTerm S 
