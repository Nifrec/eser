-- Module      : Deer.Definitions
-- Description : Definitions of relation representations, mappings between, etc.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
open import Level
open import Data.Bool hiding (_≤_)
open import Data.Nat
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Relation.Binary.Structures
open import Data.Fin hiding (_≤_)
open import Data.Vec hiding (restrict)
open import Data.Nat.Properties using (≤-<-trans)
open import Data.Fin.Properties using (toℕ<n)

--open import Relation.Nullary
--open ≡-Reasoning
--open import Data.Nat.Properties
--open import Data.Sum
--open import Data.Fin
--open import Data.Fin.Properties
--open import Data.Fin.Induction
--open import Data.Unit
--open import Data.Empty
--open import Data.List
--open import Data.List.Relation.Unary.AllPairs using (AllPairs)
--open import Data.List.Relation.Unary.All using (All)
--open import Data.List.Relation.Binary.Suffix.Heterogeneous using (Suffix)
--open import Data.List.Membership.Propositional using (_∈_ ; _∉_ )
--open import Data.List.Membership.Propositional.Properties using (∈-lookup)
--open import Data.List.Relation.Unary.Any using (Any)

module Deer.Definitions where

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

_⊢_~_ : DecRel → Rel ℕ 0ℓ
R ⊢ n ~ m = R n m ≡ true

-- Decidable equivalence relations.
DecEquiv : Set
DecEquiv = Σ[ R ∈ DecRel ]( IsEquivalence (R ⊢_~_) )

-- Proposition on a relation (property of a relation).
RelProp : Set₁
RelProp = DecRel → Set

-- Predicate that a relation satisfies a proposition (i.e. has a property).
RelSat : DecRel → RelProp → Set
RelSat R P = P R

-- Equivalence relations that also satisfy proposition P.
DecEquivThatSats : RelProp → Set
DecEquivThatSats P = Σ[ R ∈ DecRel ] (IsEquivalence (R ⊢_~_) × RelSat R P)

--------------------------------------------------------------------------------
-- Normal-form functions and globally-defined properties of them.
--------------------------------------------------------------------------------
-- Property of a function.
FunProp : Set₁
FunProp = (ℕ → ℕ) → Set

-- Proof that a function has a property.
FunSat : (ℕ → ℕ) → FunProp → Set
FunSat f P = P f

-- Coherence constraint on normal form functions: 
-- the normal form of n is always smaller or equal to n,
-- i.e., has been explored earlier.
-- This is necessary when building equivalence relations by inductively
-- assigning each n ∈ ℕ to its normal form.
NLeq : FunProp
NLeq f = (n : ℕ) → f n ≤ n

-- Coherence constraint on normal form functions: 
-- the normal form of a normal form is itself.
NFix : FunProp
NFix f = (n : ℕ) → f (f n) ≡ f n

NFFun : Set
NFFun = Σ[ f ∈ (ℕ → ℕ) ]( NLeq f × NFix f)


NFFunThatSats : FunProp → Set
NFFunThatSats P = Σ[ f ∈ (ℕ → ℕ) ] ( NLeq f × NFix f × FunSat f P)


--------------------------------------------------------------------------------
-- Normal-form functions and locally-properties of them.
--------------------------------------------------------------------------------
-- Get the first n outputs of a function ℕ → ℕ as a vector.
-- Equivalently, restrict the domain to {0, 1, ..., n-1}.
restrict : (n : ℕ) → (ℕ → ℕ) → Vec ℕ n
restrict 0 f = []
restrict (suc n) f = (f n) ∷ (restrict n f)


-- Decidable locally defined property.
-- For each n, judge whether the restriction of a function ℕ → ℕ
-- to {0, ..., n} satisfies the property.
LocProp : Set₁
LocProp = (n : ℕ) → Vec ℕ n → Set

-- Proposition that all restrictions of a function satisfy a
-- locally defined property.
LocSat : (ℕ → ℕ) → LocProp → Set
LocSat f P = (n : ℕ) → P n (restrict n f)

-- Local version of NLeq: f m ≤ m for all m,
-- where f m is encoded as the value of a vector at index 0.
NFLeqLoc : LocProp
NFLeqLoc n v = (m : Fin n) → lookup v m ≤ toℕ m

--NFLoc : LocProp
--NFLoc n v = (m : Fin n) → Σ[ nfleq ∈ (lookup v m ≤ toℕ m) ](lookup v (lookup 

-- Local version of NFix : f (f m) ≡ f m for all m.
-- Technical issue: when not assuming f m ≤ m, then f m > n is possible,
-- which means that we cannot lookup `f m` as vector index.
-- If LocSat f NFLeqLoc then this can, of course, never happen.
-- But I wanted to define NFFixLoc independently from NFLeqLoc,
-- so it has the conditional form:
--      "if f m is an index of the vector then f (f m) ≡ f m".
NFFixLoc : LocProp
NFFixLoc n v = (m : Fin n) 
             → (q : (lookup v m ≤ toℕ m)) 
             → lookup v (fromℕ< (≤-<-trans q (toℕ<n m))) ≡ lookup v m

NFFunThatLocSats : LocProp → Set
NFFunThatLocSats P = Σ[ f ∈ (ℕ → ℕ) ] (
      LocSat f NFLeqLoc 
    × LocSat f NFFixLoc 
    × LocSat f P)
