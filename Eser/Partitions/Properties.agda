-- Module      : Eser.Partitions.Properties
-- Description : Properties of the equivalences created in Parititions.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Level hiding (suc)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Data.Empty
open import Data.Fin using (Fin ; toℕ ; fromℕ<)
open import Data.Fin.Properties hiding (≤-refl ; ≤-trans)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)
open import Data.Vec as Vec
open import Data.Vec.Properties
open import Function hiding (_↔_)

open import Eser.Logic
--open import Eser.Aux using (restIsProofIrrel ; uip ; m<n→Sm<n⊎Sm≡n ; m<m+1+n)
open import Eser.Equivalences.Notation
open import Eser.Partitions
--open import Eser.Equivalences.Properties

module Eser.Partitions.Properties {A : Set} (p : Partition A) where

open PartToEnumImpl {A} p renaming (f to enc ; f⁻¹ to dec)

--open EquivShorthands (partitionToEnum p)

chunksum-lower-bound
    : (i : ℕ)
    → i ≤ ⨁ i
chunksum-lower-bound 0 = ≤-refl
chunksum-lower-bound (suc i) = subst (suc i ≤_) (sym eq) H₀
    where
        n : ℕ
        n = proj₁ $ chunks i
        eq : ⨁ (suc i) ≡ suc (⨁ i + n)
        eq =
            ≡begin 
                ⨁ (suc i)
            ≡⟨⟩
                ⨁ i + suc n
            ≡⟨ +-suc (⨁ i) n ⟩
                suc (⨁ i + n)
            ≡∎
        IH : i ≤ ⨁ i
        IH = chunksum-lower-bound i

        H₀ : suc i ≤ suc (⨁ i + n)
        H₀ = s≤s (≤-trans IH (m≤m+n (⨁ i) n))
            

-- The ℕ-encoding of an element of chunk i is always at least as great as i.
enc-larger-than-chunkidx
    : (i : ℕ)
    → (j : SubIdx chunks i)
    → i ≤ enc (chunks !!! (i , j)) 
enc-larger-than-chunkidx i j = subst (i ≤_) (sym $ f-chunks i j) H
    where
        H : i ≤ ⨁ i + toℕ j 
        H = ≤-trans (chunksum-lower-bound i) (m≤m+n (⨁ i) (toℕ j))

