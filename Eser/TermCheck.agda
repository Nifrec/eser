-- Module      : Eser.TermCheck
-- Description : Does termination checker work with implicit arguments?
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- 16 September 2026
-- 
-- Does the termination checker dislike implicit arguments?
-- No, it doesn't seem to be the problem...

open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Data.Empty
open import Data.Fin using (Fin ; _↑ˡ_ ; _↑ʳ_ )
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)
open import Data.Vec as Vec
open import Data.Vec.Properties
open import Data.List.Membership.Propositional
open import Data.List renaming (_∷_ to _∷L_) hiding (sum)
open import Function hiding (_↔_)

module Eser.TermCheck where

f : {n m : ℕ} → n ≡ n → m ≡ m → ℕ
f {0} {0} _ _ = 0
f {0} {suc m} _ _ = 1
f {suc n} {0} _ _ = f {n} {0} refl refl
f {suc n} {suc m} eq-n eq-m = f {n} {suc m} refl eq-m + f {suc n} {m} eq-n refl
