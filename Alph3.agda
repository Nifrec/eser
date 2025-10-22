-- Module      : StreamGrid.Alphabet
-- Description : Representation of alphabets of atomic path pieces.
-- Copyright   : (c) Lulof Pirée, 2025
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- Philosophically: what is an alphabet?
-- It is a set A with the following properties:
-- 1. It is not empty.
-- 2. We can form lists (strings) over it.
-- 3. It is finite.
-- 4. It is linearly ordered 
--  (hence strings over A are lexicographically ordered).

-- TODO: figure out how to get the module structure correct.
module Alph3 where

-- TODO: probably not all of these are needed.
open import Data.Bool hiding (_≤_; _≤?_)
open import Data.List
open import Data.Nat
open import Data.Nat.Properties
open import Data.Product
open import Data.Fin
open import Data.Sum
open import Data.Unit
open import Data.Vec
open import Data.String
open import Level using (0ℓ)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary

Alphabet : ℕ → Set
Alphabet n = Fin (suc n)

NamedAlphabet : ℕ → Set
NamedAlphabet n = (Alphabet n) × (Fin (suc n) → String)

-- Very terse definition of an algebra.
-- Interpretation: if `(n , c)` is an algebra then:
-- * Its maximum arity of a constructor is `m`.
-- * The number of constructors of arity `m` with `0 ≤ m < n` is `c m`.
Algebra : Set
Algebra = Σ[ n ∈ ℕ ] (Fin (suc n) → ℕ)

maxArity : Algebra → ℕ
maxArity = proj₁

numConstr : (A : Algebra) → (Fin (suc (maxArity A)) → ℕ)
numConstr = proj₂

-- Restrict a function from a set with n+1 elements to a set with n elements.
constrain : {P : Set} → {n : ℕ} → (Fin (suc n) → P) → (Fin n → P)
constrain f m = f (inject₁ m)

-- Fold a finite set of n+1 elements using a binary operator.
-- This folds the greatest element to the left.
-- E.g., when folding `Fin 3` using `f` and `_+_`, the outcome is
-- `(f 2) + (f 1) + (f 0) + p`.
-- Note: the `fold` and `fold′` functions in `Data.Fin.Base` seem
-- to do something wholly different.
fold′′ : {P : Set} → {n : ℕ} → (Fin (suc n) → P → P) → P → P
fold′′ {P} {zero} comb p = comb zero p
fold′′ {P} {suc n} comb p = comb (fromℕ (suc n)) (fold′′ {P} {n} 
    (constrain comb) p)

-- Counting the number of elements in a set with 3+1 elements
-- should give 4.
checkFold1 : fold′′ {ℕ} {3} (λ x p → suc p) 0 ≡ 4
checkFold1 = refl

-- 3 + 2 + 1 + 0 + 0 = 6.
checkFold2 : fold′′ {ℕ} {3} (λ x p →  Data.Nat._+_ (toℕ x) p) 0 ≡ 6
checkFold2 = refl

-- This check verifies the elements are folded in the right order
-- (the previous checks use `_+_` which is commutative).
checkFold3 : fold′′ {List ℕ} {3} (λ x p → (toℕ x) ∷ p) [] ≡ (3 ∷ 2 ∷ 1 ∷ 0 ∷ [])
checkFold3 = refl


---- Total number of constructors (of any arity) in an algebra.
totNumConstr : Algebra → ℕ
totNumConstr (zero , c) = c (fromℕ zero)
totNumConstr (suc n , c)
    = fold′′ {ℕ} {suc n} (λ x sum → Data.Nat._+_ (toℕ x) sum) 0

-- Type of functions that gives names to the constructors in an algebra.
AlgNaming : Algebra → Set
AlgNaming A = Vec String (totNumConstr A)

-- Sanity check: binary trees that have both red and black internal nodes.
-- So these trees have 3 constructors.
rbTreeNumConstr : Fin 3 → ℕ
rbTreeNumConstr zero = 1 -- Single constructor for leafs.
rbTreeNumConstr (suc zero) = zero
rbTreeNumConstr (suc (suc zero)) = 2 -- Two colours of binary nodes.
RBTreeAlg : Algebra 
RBTreeAlg = (2 , rbTreeNumConstr)
-- We can make sense of the constructors like this:
rbTreeNaming : AlgNaming RBTreeAlg
rbTreeNaming = "leaf" ∷ "red" ∷ "black" ∷ []
-- Check correctness of number of constructors:
checkRBTreeAlg : totNumConstr RBTreeAlg ≡ 3
checkRBTreeAlg = refl

-- Converting an Algebra to an actual Agda type.
-- Each constructor becomes a constructor with the correct arity.
data ToType (A : Algebra) : Set where
    construct
        : (arity : Fin (suc (maxArity A)))      
        --^ Give desired arity.
        → (constr : Fin ((numConstr A) arity))  
        --^ Pick desired constructor with that arity.
        → Vec (ToType A) (toℕ arity)
        --^ Pick <arity> number of arguments.
        → ToType A

-- Convenience function to construct the (m+1)th atomic (nullary) element.
atom : {A : Algebra} → (m : ℕ) → (m Data.Nat.< numConstr A zero) → ToType A
atom m m<M = construct zero (fromℕ< m<M) []
