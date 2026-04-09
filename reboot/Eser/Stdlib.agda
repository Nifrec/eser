-- Module      : Eser.Stdlib
-- Description : Things from the standard library
--------------------------------------------------------------------------------
-- Some definitions that exist in the standard library give an error when I try
-- to import them, Agda thinks they are not defined in the standard library.
-- This is a mere technical issue;
-- some bug in Adga, in my installation, a version mismatch, etc.
--
-- This file is a (hopefully temporary) workaround that just copies the whole
-- definitions.
--
-- I (Lulof Pirée) do not claim authership of those definitions,
-- they are from the stdlib!
open import Relation.Binary.PropositionalEquality.Core as ≡
  using (_≡_; _≢_; refl; sym; trans; cong; cong₂; subst; _≗_)
open import Axiom.UniquenessOfIdentityProofs using (module Decidable⇒UIP)
open import Data.Fin.Properties
open import Data.Fin
open import Data.Nat
open import Relation.Binary.Definitions using (Irrelevant)

module Eser.Stdlib where

fin-≡-irrelevant : {n : ℕ} → Irrelevant {A = Fin n} _≡_
fin-≡-irrelevant = Decidable⇒UIP.≡-irrelevant Data.Fin.Properties._≟_

-- This is defined in the stdlib, according to the documentation,
-- but for some reason I cannot import it.
∸-suc : {n m : ℕ} → m Data.Nat.≤ n → suc n ∸ m ≡ suc (n ∸ m)
∸-suc z≤n       = refl
∸-suc (s≤s m≤n) = ∸-suc m≤n
