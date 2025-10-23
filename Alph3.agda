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
open import Data.Empty
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
-- * Its maximum arity of a constructor is `n`.
-- * The number of constructors of arity `m` with `0 < m < n` is `c m`.
-- * The number of constructors of arity `zero` is `1 + (c zero)`.
-- * The number of constructors of arity `n` is `1 + (c n)`.
--
-- Rationale behind last two points:
-- Empty algebras do not make sense,
-- so the first nullary constructor is assumed to always be implicitly
-- present. 
-- Hence there are `1 + (c zero)` nullary constructors.
--
-- A maximum arity of `n` without any n-arty constructor likewise makes
-- no sense, so the first n-arty constructor is always implicitly present
-- as well.
Algebra : Set
Algebra = Σ[ n ∈ ℕ ] (Fin (suc n) → ℕ)

maxArity : Algebra → ℕ
maxArity = proj₁

-- Increment the output of a function by 1 if the input is 0,
-- for all other inputs retain the original output.
incrOutpAtZero : {n : ℕ} → (Fin n → ℕ) → (Fin n → ℕ)
incrOutpAtZero f zero = suc (f zero)
incrOutpAtZero f (suc m) = f (suc m)

-- Increment the output of a function by 1 if the input is the maximum possible,
-- for all other inputs retain the original output.
incrOutpAtMax : {n : ℕ} → (Fin n → ℕ) → (Fin n → ℕ)
-- If a set has `1+n` elements then the largest element is `n`.
--incrOutpAtMax {suc n} f (fromℕ n) = suc (f (fromℕ n))
--incrOutpAtMax {suc n} f m = f m
incrOutpAtMax {suc n} f m with (toℕ m) ≡ᵇ n
... | true = suc (f m)
... | false = f m

numConstr : (A : Algebra) → (Fin (suc (maxArity A)) → ℕ)
numConstr A = incrOutpAtMax (incrOutpAtZero (proj₂ A))

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

-- Nonzero base case:
-- 3 + 2 + 1 + 0 + 10 = 16.
checkFold4 : fold′′ {ℕ} {3} (λ x p →  Data.Nat._+_ (toℕ x) p) 10 ≡ 16
checkFold4 = refl 

---- Total number of constructors (of any arity) in an algebra.
totNumConstr : Algebra → ℕ
totNumConstr (zero , c) = (numConstr (zero , c) (fromℕ zero))
totNumConstr (suc n , c)
    = fold′′ {ℕ} {suc n} (λ x sum → Data.Nat._+_ (c' x) sum) 0
    where
        c' = numConstr (suc n , c)

-- Type of functions that gives names to the constructors in an algebra.
AlgNaming : Algebra → Set
AlgNaming A = Vec String (totNumConstr A)

-- Sanity check: binary trees that have both red and black internal nodes.
-- So these trees have 3 constructors.
rbTreeNumConstr : Fin 3 → ℕ
rbTreeNumConstr zero = 0 -- Single IMPLICIT constructor for leafs.
rbTreeNumConstr (suc zero) = zero
rbTreeNumConstr (suc (suc zero)) = 1 
    --^ Two colours of binary nodes. First is implicit.
RBTreeAlg : Algebra 
RBTreeAlg = (2 , rbTreeNumConstr)
-- We can make sense of the constructors like this:
rbTreeNaming : AlgNaming RBTreeAlg
rbTreeNaming = "leaf" ∷ "red" ∷ "black" ∷ []
-- Check correctness of number of constructors:

checkRB1 : numConstr RBTreeAlg zero ≡ 1
checkRB1 = refl
checkRB2 : numConstr RBTreeAlg (suc zero) ≡ 0
checkRB2 = refl
checkRB3 : numConstr RBTreeAlg (suc (suc zero)) ≡ 2
checkRB3 = refl
checkRB4 : totNumConstr RBTreeAlg ≡ 3
checkRB4 = refl

-- Natural numbers as the algebra (zero, suc) : ℕ → 1 + ℕ
NatAlgConstr : Fin 2 → ℕ
NatAlgConstr zero = 0
    --^ Single implicit constructor for `zero`.
NatAlgConstr (suc zero) = 0
    --^ Single implicit constructor for `suc`.
NatAlg : Algebra 
NatAlg = (1 , NatAlgConstr)
checkNatAlg1 : numConstr NatAlg zero ≡ 1
checkNatAlg1 = refl
checkNatAlg2 : numConstr NatAlg (suc zero) ≡ 1
checkNatAlg2 = refl
checkNatAlg3 : totNumConstr NatAlg ≡ 2
checkNatAlg3 = refl

-- Trees with three kinds of leafs, two kinds of nodes with 1 child, 
-- and one kind of node with 2 children.
-- Reason: check number of constructors that are not nullary or max-ary.
MixTreeConstr : Fin 3 → ℕ
MixTreeConstr zero = 2
    --^ Three constructors for leafs.
MixTreeConstr (suc zero) = 2
    --^ Two constructors for 1-child nodes.
MixTreeConstr (suc (suc zero)) = 0
    --^ Single implicit constructor for 2-child nodes.
MixTree : Algebra 
MixTree = (2 , MixTreeConstr)
checkMixTree1 : numConstr MixTree zero ≡ 3
checkMixTree1 = refl
checkMixTree2 : numConstr MixTree (suc zero) ≡ 2
checkMixTree2 = refl
checkMixTree3 : numConstr MixTree (suc (suc zero)) ≡ 1
checkMixTree3 = refl
checkMixTree4 : totNumConstr MixTree ≡ 6
checkMixTree4 = refl

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

----------- ALL STUFF BELOW IS WIP AND BROKEN ----------------------------------

NonEmptyAlg : Algebra → Set
NonEmptyAlg A with (0 Data.Nat.<? totNumConstr A)
... | yes _ = ⊤
... | no _ = ⊥

AlgToAlph : (A : Algebra) → NonEmptyAlg A → Alphabet (Data.Nat.pred (totNumConstr A))
-- Agda doesn't yet know that (suc (pred N)) = N
-- where N is num constructors.
-- Need to prove totNumConstr is of the form (suc N).
AlgToAlph A _ = {! Fin (totNumConstr A) !}
