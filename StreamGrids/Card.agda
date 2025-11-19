-- Module      : StreamGrids.Card
-- Description : Tools for working with sets of different cardinalities.
-- Copyright   : (c) Lulof Pirée, 2025
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------

-- TODO: probably not all of these are needed.
open import Data.Bool hiding (_≤_; _≤?_)
open import Data.Empty
open import Data.Fin hiding (_<_)
open import Function using (Inverseᵇ)
open import Data.List
open import Data.Nat hiding (_<_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Data.Vec
open import Level using (0ℓ)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary


module StreamGrids.Card where

--------------------------------------------------------------------------------
-- ℕ∞ is the type of cardinalities.
--------------------------------------------------------------------------------

-- Natural numbers extended with a top element '∞' (w.r.t. the '<' relation).
-- #TODO: check if this already exist in the standard library?
data ℕ∞ : Set where
    fin     : ℕ → ℕ∞
    ∞       : ℕ∞

suc∞ : ℕ∞ → ℕ∞
suc∞ (fin n) = fin (suc n)
suc∞ ∞ = ∞

_<∞_ : Rel ℕ∞ 0ℓ
fin n <∞ fin m  = n Data.Nat.< m
fin n <∞ ∞      = ⊤
∞     <∞ fin m  = ⊥
∞     <∞ ∞      = ⊥

--------------------------------------------------------------------------------
-- Tools for convering between cardinalities and sets.
--------------------------------------------------------------------------------

-- Map a cardinality in Bigℕ to the prefix of the natural numbers
-- with that cardinality.
cardToSet : ℕ∞ → Set
cardToSet (fin 0) = ⊥
cardToSet (fin (suc n)) = Fin (suc n) -- Fin 0 cannot be constructed!
cardToSet ∞ = ℕ
 
-- Get the default < relation on a prefix of ℕ.
cardTo< : {n : ℕ∞} → Rel (cardToSet n) 0ℓ
cardTo< {fin 0} ()
cardTo< {fin (suc n)} = Data.Fin._<_
cardTo< {∞} = Data.Nat._<_

cardToSuc : {n : ℕ∞} → (m : cardToSet n) → cardToSet (suc∞ n) 
cardToSuc {fin 0} ()
cardToSuc {fin (suc n)} m = Data.Fin.suc m
cardToSuc {∞} m = Data.Nat.suc m

-- Return one lower number if it exists, but return 0 as predecessor of 0.
cardToPred : {n : ℕ∞} → (m : cardToSet n) → cardToSet n
cardToPred {fin 0} ()
cardToPred {fin (suc n)} zero = zero
cardToPred {fin (suc n)} (suc m) = inject₁ m
cardToPred {∞} zero = zero
cardToPred {∞} (suc m) = m


clipSuc : {n : ℕ} → Fin n → Fin n
clipSuc {suc n} m with n Data.Nat.≟ toℕ m
... | yes _ = m
... | no p = let q = negTransport p (lemma {n} {m}) in
    lower₁ (suc m) q
    where
        lemma : {n : ℕ} {m : Fin (suc n)} 
              → (suc n ≡ toℕ ( suc m)) 
              → (n ≡ toℕ m)
        lemma {n} {m} r = suc-injective r
        negTransport : {A B : Set} → ¬ B → (A → B) → ¬ A
        negTransport {A} {B} ¬B f a = ⊥-elim (¬B (f a))

-- Return one greater element if it exists, return the maximum if the set is
-- finite and the input is the maximum element.
cardToClipSuc : {n : ℕ∞} → (m : cardToSet n) → cardToSet n
cardToClipSuc {fin 0} ()
cardToClipSuc {fin (suc n)} m = clipSuc m
cardToClipSuc {∞} m = suc m

-- Compare a natural number for equality n to a number m in (cardToSet c).
ℕequalsCardToSetElem : {c : ℕ∞} → ℕ → (m : cardToSet c) → Set
ℕequalsCardToSetElem {fin (suc c)} n m  = (toℕ m) ≡ n
ℕequalsCardToSetElem {∞} n m = n ≡ m
