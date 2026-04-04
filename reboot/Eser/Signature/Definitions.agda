-- Module      : Eser.Signature.Definitions
-- Description : Definition of signature, open terms and closed terms.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------

open import Level
open import Data.Bool hiding (_≤_ ; _<_ ; _≤?_)
open import Data.Bool.Properties
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Induction
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Relation.Binary.Structures
open import Data.Fin hiding (_+_ ; _<_ ; _≤_)
open import Data.Vec 
open import Function
open import Relation.Binary.Reasoning.Syntax
open import Data.Fin.Properties using (fromℕ<-toℕ ; toℕ-fromℕ< ; toℕ-injective)

open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)

open import Eser.Card

module Eser.Signature.Definitions where

--------------------------------------------------------------------------------
-- New encoding of signatures
--
-- Let ℕ∞ = ℕ  ∪ {∞}.
-- A signature consists of two things:
-- 1. A number of nullary constructors, μ.
--      The collection of nullary constructors is either `Fin μ` if μ ∈ ℕ
--      xor ℕ if μ = ∞.
-- 2. A number of multiary constructors, together with a function that
--      assigns to each such constructor the number-of-arguments-minus-one.
--      Again, the set of constructors is either `Fin ζ` xor ℕ.
--
-- Particularities of this representation:
-- * No external ℕ-arguments are needed, since we can unfold constructors
--      that take a ℕ-argument into ℕ-many distinct constructors, one for each
--      argument. Note that, with this trick, we can unfold any constructor
--      taking a finite number of arguments from finite and/or enumerable sets
--      into at most ℕ-many constructors.
-- * Constructors are not sorted by their arity.
--      This allows to have arbitrary many constructors of each arity,
--      and also to have no upper bound on the maximum arity.
-- * We can ealisy recognise empty and finite term algebras:
--      * Signature 0 ζ has an empty term algebra.
--      * Signature (suc∞ μ) 0 has a finite term algebra.
--      * Signature (suc∞ μ) (suc∞ ζ) has a term algebra equivalent to ℕ.
--------------------------------------------------------------------------------

Signature : ℕ∞ → ℕ∞ → Set
Signature μ ζ = cardToSet ζ → ℕ

-- Lookup the arity of a constructor in a signature.
arity : {μ ζ : ℕ∞} → {S : Signature μ ζ} → (c : cardToSet ζ) → ℕ
arity {S = S} c = ℕ.suc (S c)

--------------------------------------------------------------------------------
-- Closed terms over a signature
--
-- Closed terms are either a nullary constructor or a multiary constructor
-- of arity m with a vector of m terms as arguments.
--
-- We annotate every term with a 'weight' to make enumerating terms easier.
-- Note that the weights pose no constraints on term formation,
-- they are just calculated after giving arguments to constructors.
-- So it is still easy to see that we can create the same terms 
-- as without using weights.
-- Rules of weights: the weight of a term is the sum of:
--      * 1 
--      * the index of the constructor (in cardToSet μ or cardToSet ζ resp.).
--      * the sum of the weights of the inductive arguments.
-- Adding the '1' ensures that all constructors (even unary ones) 
-- are always heavier than any of their arguments.
--
-- The original 'Lih.agda' file used only closed terms,
-- and stored inductive arguments as a vector (whose length matches the
-- arity of the used constructor); this was to be compared against the
-- alternative of a function `args : arity → Terms S`:
-- * If two vectors have equal elements, then they are equal.
--      For functions this is not the case, at least not without assuming
--      function extensionality, and this would allow to build 'distinct'
--      terms with the same arguments.
-- * Because of the previous point, proving the isomorphism from Terms to ℕ
--      is easier.
-- * Functions allow to define a subterm relation, since the termination checker
--      is OK with evaluating a function, but not with the _∈_ relation on
--      vectors. On the subterm relation one can define well-founded recursion.
--      However, this all is not necessary, since we can still do 
--      well-founded (ℕ , <) recursion on the weights; subterms have lower
--      weights anyway!
--
-- In hindsight, vectors were not so convenient during enumeration because
-- counting the number of possible vectors of lighter arguments, whose sum
-- of weights is the current term's weight, is a lot of work to implement in
-- Agda (it is possible, since <-rec on the weights allows to show the arguments
-- come from finite sets, and then some combinatorics, etc.
-- But the number of data conversions, arithmetic rewrites and other things that
-- that thorny is Agda, just wasn't fun).
--
-- Open terms allow to represent constructors with a few arguments applied,
-- but not as many as their arity.
-- Now arguments are given one-by-one, and the combinatorial problem
-- is simplified to just counting the number of arguments a
-- and open terms t such that wₐ + wₜ ≡ w.
-- We use <-rec to show both a and t are drawn from finite sets.
--------------------------------------------------------------------------------

-- OpenTerms S w n are the terms over signature S
-- * whose total weight (so far) is w
-- * that still need n more arguments to become a closed term
--      (i.e., to become a constructor with exactly as many inductive
--      arguments as its own arity).
data OpenTerms {μ ζ : ℕ∞} (S : Signature μ ζ) : ℕ → ℕ → Set where
    mk-nullary 
        : (c : cardToSet μ) 
        → OpenTerms S (ℕ.suc $ cardToℕ c) 0
    mk-multiary 
        : (c : cardToSet ζ) 
        → OpenTerms S (ℕ.suc $ cardToℕ c) (arity {μ} {ζ} {S = S} c)
    -- Give a closed term as next argument to a strictly open term.
    giveArg 
        : {wₜ : ℕ} 
        → {wₐ : ℕ} 
        → {m : ℕ} 
        → (t : OpenTerms {μ} {ζ} S wₜ (ℕ.suc m))
        → (a : OpenTerms {μ} {ζ} S wₐ 0)
        → OpenTerms {μ} {ζ} S (wₐ + wₜ) m
    
-- Closed terms: open terms needing no more arguments.
ClosedTerms : {μ ζ : ℕ∞} (S : Signature μ ζ) → ℕ → Set
ClosedTerms {μ} {ζ} S w =  OpenTerms {μ} {ζ} S w 0

-- *All* closed terms over S.
AllTerms : {μ ζ : ℕ∞} (S : Signature μ ζ) → Set
AllTerms {μ} {ζ} S = Σ[ w ∈ ℕ ] (ClosedTerms {μ} {ζ} S w)

