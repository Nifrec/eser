-- Module      : Eser.NewSigStream.Partitions
-- Description : COnversion from bijective partitions to enumerations.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- If a type A can be divided into a ℕ-indexed collection
-- of non-empty finite sets, such that every term of A occurs exactly once
-- in exactly one such set, then one obtains an equivalence A ≃ ℕ.
--
-- This is similar to how the Haskell-library "Feat" represents enumerations,
-- but here it is dependently typed and proven internally correct.
-- (See Duregård, Jonas, et al. 
--  ‘Feat: Functional Enumeration of Algebraic Types’. 
--  ACM SIGPLAN Notices, vol. 47, no. 12, Sep. 2012, pp. 61–72. 
--  ACM Digital Library, https://doi.org/10.1145/2430532.2364515.)

open import Level hiding (suc)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Data.Empty
open import Data.Fin using (Fin ; _↑ˡ_ ; _↑ʳ_ ; splitAt ; join)
open import Data.Fin.Properties using (join-splitAt)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)
open import Data.Vec as Vec hiding (splitAt)
open import Data.Vec.Properties
open import Data.List.Membership.Propositional
open import Data.List renaming (_∷_ to _∷L_) hiding (sum ; splitAt)
open import Function hiding (_↔_)

open import Eser.Logic
open import Eser.Aux using (restIsProofIrrel ; uip)
open import Eser.Equivalences.Notation

module Eser.NewSigStream.Partitions where

Chunking : (A : Set) → Set
Chunking A = ℕ → Σ[ m ∈ ℕ ] Vec A (suc m)

SubIdx : {A : Set} → Chunking A → ℕ → Set
SubIdx f i = Fin (suc $ proj₁ $ f i)

Idx : {A : Set} → Chunking A → Set
Idx f = Σ[ i ∈ ℕ ] (SubIdx f i)

_!!!_ : {A : Set} → (f : Chunking A) → Idx f → A
f !!! (i , j) = Vec.lookup (proj₂ $ f i) j

record Partition (A : Set) : Set where
    field
        chunks : Chunking A
        -- Each element occurs in some chunk.
        complete : (a : A) → Σ[ ij ∈ (Idx chunks) ] a ≡ chunks !!! ij
        -- Chunks are disjoint and have no duplicates,
        -- i.e., elements occur in at most one chunk and therein at most once.
        unique 
            : (ij hk : Idx chunks) 
            → (chunks !!! ij) ≡ (chunks !!! hk) 
            → ij ≡ hk

partitionToEnum : {A : Set} → Partition A → A ≃ ℕ
partitionToEnum {A} p = ?
