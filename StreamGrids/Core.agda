-- Module      : StreamGrids.Core
-- Description : Core definitions and functions
-- Copyright   : (c) Lulof Pirée, 2025
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- Contents of this file:

module StreamGrids.Core where

-- TODO: probably not all of these are needed.
open import Data.Bool hiding (_≤_; _≤?_)
open import Data.Empty
open import Data.Fin
open import Function using (Inverseᵇ)
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.String
open import Data.Sum
open import Data.Unit
open import Data.Vec
open import Level using (0ℓ)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

open import StreamGrids.Chain
open import StreamGrids.Enumeration

--------------------------------------------------------------------------------
-- Auxiliary definitions
--------------------------------------------------------------------------------
-- Biimplication A ←→ B : two types can prove each other.
_iff_ : {ℓ : Level.Level} → (A B : Set ℓ) → Set ℓ
A iff B = (A → B) × (B → A)

--------------------------------------------------------------------------------
-- Signoids
-- The raw "strings" that we later (when building a StreamGrid on top of it)
-- will quotient by equalities to obtain our desired type.
--
-- For example, a finitely generated monoid over {a, b} is (1) a signature
-- with three nullary constructors (the unit, a and b),
-- and one binary constructor _·_ ,
-- together with (2) equalities between the signature's terms
-- (e.g., ensuring (a·a)·b ≈ a·(a·b), which are *not* equal signature terms,
-- but equal as monoid elements.
--
-- Signoids are generalisation of, among others, the following things:
--  * Strings over a fixed alphabet.
--  * Signatures with finitely many constructors of finite arity.
--  * Enumerable inductive types.
--
-- There are two ways to give a signoid A.
-- Both ways give an enumeration `enum : ℕ → A` and a 'subterm relation'
-- `_⊂_ : A → A → Type` such that `x ⊂ y` ensures `enum x < enum y`.
-- (I.e., subterms have lower numbers).
-- The last piece is either
-- 1. an inverse to `enum`.
-- or
-- 2. a relation _<_ that is a Chain and a superrelation of _⊂_,
--  s.t. `enum` is also monotone in _<_.
--
-- The data pieces 1. and 2. can be constructed from each other,
-- so only one of the two is strictly necessary.
-- However, these canonical constructions are not efficiently implemented:
-- they are brute-force enumerate till you found the desired number,
-- and `(x, y) ↦ enum x < enum y`, respectively.
-- Therefore we allow the user is allowed to 
-- provide custom (optimised) implementations for both if they so desire.
--------------------------------------------------------------------------------
open import Relation.Binary.Reasoning.Syntax using (SubRelation)

-- #TODO: this definition is still WIP,
-- the type may change (maybe enum is needed).
-- Intuition in the context of signatures:
-- if `c(a)` is a term consisting of constructor `c` 
-- taking argument `a` (a tree),
-- and there exist a smaller tree `a'`, then `c(a')` is also an existing term,
-- and in the lexicographical order we have `c(a') < c(a)`.
-- In general, _⊂_ is a subterm relation of _<_ if:
-- (1) it is a subrelation that satisfies
-- (2) if `x ⊂ y` and `x' < x`, then there exists a `y'` with the same
--      ⊂-children as `y`, except for also having `x'` and possibly not `x`,
--      and `y' < y`.
IsSubTermRelat 
    : {ℓ : Level.Level}
    → {A : Set ℓ} 
    → (_<_ : Rel A ℓ)
    → SubRelation _<_ ℓ ℓ
    → Set ℓ
IsSubTermRelat {ℓ} {A} _<_ 
    record { S = _⊂_ ; IsS = IsS ; IsS? = IsS? ; extract = extract } =
    {x y x' : A} → (x ⊂ y) → (x' < x) → Σ[ y' ∈ A ](
        (y' < y)
        ×
        (x' ⊂ y')
        ×
        ({x'' : A} → (x'' ≢ x) → (x'' ≢ x') → ((x'' ⊂ y) iff (x'' ⊂ y')))
        -- `y'` same subterms as `y` except possibly not `x` and extra `x'`.
        )

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

record Signoid 
    {ℓ : Level.Level} 
    {A : Set ℓ} 
    (_<_ : Rel A ℓ) 
    (_⊂_ : SubRelation _<_ ℓ ℓ) 
    : Set ℓ where
    field
        numEl    : ℕ∞
        enum     : (cardToSet numEl) → A
        monotone : (n m : (cardToSet numEl)) → (cardTo< n m) → (enum m) < (enum n)
        --^ I tried defining this also as 
        --  `(n : cardToSet numEl) → (enum cardToPred n) < (enum n)`,
        --  but this runs into issues when n=0. 
        --  Using suc instead leads to the same problem when n is the max.
        mono : Monotonic₁ (cardTo<) (_<_) enum
        surj     : (a : A) → Σ[ n ∈ cardToSet numEl ]( enum n ≡ a)
        chain : Chain _<_
        subterm : IsSubTermRelat _<_ _⊂_ 
        getIdx : A → cardToSet numEl
        inv : Inverseᵇ _≡_ _≡_ enum getIdx
