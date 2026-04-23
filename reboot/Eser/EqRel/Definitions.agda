-- Module      : Eser.EqRel.Definitions
-- Description : Representations of and predicates on equivalence relations.
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
open import Relation.Binary.Structures
open import Data.Fin hiding (_≤_ ; _≤?_)
open import Data.Vec hiding (restrict)
open import Data.Nat.Properties using (≤-refl ; ≤-trans ; ≤-<-trans ; n≤0⇒n≡0 
                                       ; n≤1+n ; m≤n⇒m<n∨m≡n ; _≤?_ ; ≰⇒≥)
open import Data.Fin.Properties using (toℕ<n)
open import Relation.Nullary -- Needed for with-abstractions on decidable ≡.
open import Function hiding (_↔_)
open import Data.List hiding (lookup ; last)

open import Eser.Aux
open import Eser.Logic using (elimCaseLeft ; elimCaseRight)

module Eser.EqRel.Definitions where

--------------------------------------------------------------------------------
-- Relations on ℕ
--------------------------------------------------------------------------------

-- Relations as functions. 
-- This Bool-valued representation is always proof-irrelevant
-- and decidable, and more convenient when proving homotopy between relations.
-- The Agda stdlib lets a relation output a Set, which is annoying when
-- trying to show a homotopy that does not care about proof implementations.
-- See below `_ ⊢ _ ~ _` for a conversion to the stdlib's representation.
DecRel : Set
DecRel = ℕ → ℕ → Bool

_⊢_~_ : {A : Set} → (A → A → Bool) → Rel A 0ℓ
R ⊢ n ~ m = R n m ≡ true

-- Decidable equivalence relations.
DecEquiv : Set
DecEquiv = Σ[ R ∈ DecRel ]( IsEquivalence (R ⊢_~_) )

-- Type of predicates on a relation 
-- (Not necessarily proof irrelevant
-- since that's simply a bit inconvenient to implement in Agda --
-- the `Prop` sort is not vanilla and experimental,
-- and adding proofs of proof-irrelevance via Σ is overcomplicating things).
RelPred : Set₁
RelPred = DecEquiv → Set

-- Equivalence relations that also have a given property.
DecEquivWithProp : RelPred → Set
DecEquivWithProp P = Σ[ R ∈ DecRel ] Σ[ Req ∈ IsEquivalence (R ⊢_~_) ] (P (R , Req))

--------------------------------------------------------------------------------
-- Normal-form functions and globally-defined properties of them.
--------------------------------------------------------------------------------
-- Property of a function.
FunPred : Set₁
FunPred = (ℕ → ℕ) → Set

-- Coherence constraint on normal form functions: 
-- the normal form of n is always smaller or equal to n,
-- i.e., has been explored earlier.
-- This is necessary when building equivalence relations by inductively
-- assigning each n ∈ ℕ to its normal form.
NFLeq : FunPred
NFLeq f = (n : ℕ) → f n ≤ n

-- Coherence constraint on normal form functions: 
-- the normal form of a normal form is itself.
NFFix : FunPred
NFFix f = (n : ℕ) → f (f n) ≡ f n

-- Functions ℕ → ℕ that encode an equivalence relation,
-- i.e., functions that satisfy the coherence conditions that allow
-- them to be used as a normal-form function.
NFFun : Set
NFFun = Σ[ f ∈ (ℕ → ℕ) ]( NFLeq f × NFFix f)

-- #TODO: remove?
NFFunWithProp : FunPred → Set
NFFunWithProp P = Σ[ f ∈ (ℕ → ℕ) ] ( NFLeq f × NFFix f × P f)


--------------------------------------------------------------------------------
-- Normal-form functions and locally-defined predicates on them.
--------------------------------------------------------------------------------
-- Get the first n outputs of a function ℕ → ℕ as a vector.
-- Equivalently, restrict the domain to {0, 1, ..., n-1}.
restrict : (n : ℕ) → (ℕ → ℕ) → Vec ℕ n
restrict 0 f = []
restrict (suc n) f = (f n) ∷ (restrict n f)

-- Decidable locally defined predicate.
-- For each n, judge whether the restriction of a function ℕ → ℕ
-- to {0, ..., n-1} satisfies the predicate.
LocPred : Set₁
LocPred = (n : ℕ) → Vec ℕ n → Set

-- Predicate that all restrictions of a function satisfy a
-- locally defined property.
AllRestr : (ℕ → ℕ) → LocPred → Set
AllRestr f P = (n : ℕ) → P n (restrict n f)

-- #TODO: remove?
-- Local version of NFLeq: f m ≤ m for all m,
-- where f m is encoded as the value of a vector at index 0.
NFLeqLoc : LocPred
NFLeqLoc n v = (m : Fin n) → lookup v m ≤ toℕ m

NFFunWithLocPred : LocPred → Set
NFFunWithLocPred P = Σ[ f ∈ (ℕ → ℕ) ] (
      NFLeq f
    × NFFix f
    × AllRestr f P)
