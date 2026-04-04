-- Module      : Eser.Signature.JumpEnum
-- Description : Equivalence between sums-of-fin-sets to natural numbers.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- The type Σ[ x ∈ ℕ ] Fin (f x) is equivalent to ℕ if infinitely
-- many `Fin (f x)`s are inhabited.
-- Having a function that maps from an inhabited x ∈ ℕ
-- to the next inhabited x' ∈ ℕ (so f(x) ≥ 1, f(x') ≥ 1, x' > x)
-- (and skipping over all intermediate x'' with f(x'') = 0)
-- is sufficient to establish the equivalence.

{-# OPTIONS --allow-unsolved-metas #-}

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
open import Eser.Equivalences.Notation
open import Eser.Equivalences.Properties
open import Eser.Aux
open import Eser.Signature.Definitions

module Eser.Signature.JumpEnum where

-- `iter f n a` returns fⁿ(a), i.e., f applied n times starting from a.
iter : {A : Set} → (A → A) → ℕ → A → A
iter {A} f 0 a = a
iter {A} f (suc n) a = f (iter f n a)

--------------------------------------------------------------------------------
-- Skip-over-⊥s theorem
-- A sum over a family of types is equivalent to the sum
-- over the same types except with the empty ones left out.
--
-- One could prove a more general statement than presented here,
-- but this version is most convenient for our use case.
--------------------------------------------------------------------------------

-- A function that jumps from one to the next inhabited type
-- given an ℕ-indexed family of types.
InhabitJumper : (C : ℕ → Set)  → Set
InhabitJumper C 
    = {w : ℕ} 
    → C w
    → Σ[ h ∈ ℕ ] (
       --^ Jumping distance (minus one).
       (C $ w + 1 + h) 
       --^ The destination is inhabited, ...
       × 
       ((x : ℕ) → (w < x × x < w + 1 + h) → ¬ C x) 
       --^ ... but intermediate points are not.
    )
-- Note: the argument `C w` might seem redundant.
-- For my use case it could indeed be avoided,
-- but the implementation of an actual jumper simplifies a lot if we can
-- depart from the latest inhabited point.
-- The alternative is to take multiple jumps from the first inhabited points,
-- until one reaches the first point beyond w; this is more work to prove right
-- in Agda.

-- Iterate an InhabitJumper from an inhabited starting point n₀,
-- and give the point reached after n jumps.
-- (In out use case (see below), we'll have ¬ C 0 but C 1 is inhabited, 
-- so we start with n₀ ≔ 1).
J-iter : {C : ℕ → Set} → (n₀ : ℕ) → C n₀ → (J : InhabitJumper C) → ℕ → ℕ
J-iter {C} n₀ t₀ J 0 = n₀
--J-iter {C} n₀ t₀ J (suc n) = proj₁ $ depGIter g J' n (n₀ , t₀)
J-iter {C} n₀ t₀ J (suc n) = proj₁ $ iter J' n (n₀ , t₀)
    where
        J' : Σ[ w ∈ ℕ ] C w → Σ[ w ∈ ℕ ] C w
        J' (w , t) = 
            let (h , t' , _) = J {w} t
            in
            (w + 1 + h , t')

jumpOver⊥s
    : (C : ℕ → Set)
    → (J : InhabitJumper C)
    → (¬ C 0)
    → (t₀ : C 1)
    → (Σ[ w ∈ ℕ ] C w) ≃ (Σ[ n ∈ ℕ ] (C $ J-iter 1 t₀ J n))
jumpOver⊥s _ _ _ _ = ? -- See sheet "Lih 11" backside

jumpTheoremInhabitJumper
    : {C : ℕ → Set}
    -- ^ Type of 'pitstops' the jumping function can visit.
    → (t₀ : C 1)
    -- ^ Proof the starting pitstop with index 1 is inhabited.
    → (J : InhabitJumper C)
    -- ^ Function to jump between pitstops.
    → ((w : ℕ) → Σ[ z ∈ ℕ ]( C w ≃ Fin z ))
    -- ^ Every point (incl. non-pitstops) is some finite set.
    → ((i : ℕ) → Σ[ z' ∈ ℕ ] (C (J-iter {C} 1 t₀ J i) ≃ Fin (ℕ.suc z')))
    -- ^ But when only looking at pitstops, they are inhabited finite sets.
jumpTheoremInhabitJumper = ? -- Sheet "Lih 10".

--------------------------------------------------------------------------------
-- Every signature with at least one nullary constructor and at least
-- one multiary constructor has infinitely many terms,
-- and there are infinitely many weights such that it has a term of that weight.
-- We can always build an InhabitJumper visiting exactly those weights
-- (actually, there are probably many ways to do so, but showing some
-- InhabitJumper exists is enough!)
--
-- Note: "at least one nullary and at least one multiary constructor"
-- is the same as "μ ≥ 1 and ζ ≥ 1".
-- Strictly speaking,
-- building an InhabitJumper does not require any nullary constructor,
-- But this is always required when applying it in the jumpOver⊥s
-- or in the jumpTheoremInhabitJumper (to create the argument t₀) anyway.
-- So we do require it, 
-- since having a nullary constructor makes the implementation easier.
--
-- Strategy: let c be the given multiary constructor and a₀ be the given nullary
-- constructor.
-- Then c(a₀, a₀, a₀, ... , a₀, -) : {w} → C w → C (w + 1 + h)
-- (c with a₀ applied one time fewer than its arity)
-- gives a family of terms that has a member greater than any inhabited weight.
-- (h is the index of c plus (arity(c) - 1)*(weight of a₀) = (arity(c) - 1)
-- since a₀ weights 1.
--------------------------------------------------------------------------------

module _ {μ ζ : ℕ∞} (S : Signature (suc∞ μ) (suc∞ ζ) ) where

    C = ClosedTerms {suc∞ μ} {suc∞ ζ} S
    OT = OpenTerms {suc∞ μ} {suc∞ ζ} S

    -- Given an OpenTerm with (suc n) open argument-holes and an argument a₀,
    -- apply a₀ n times to it, yielding an OpenTerm with 1 open hole.
    applyArgTillAlmostFull
        : {n : ℕ}
        → {wₜ wₐ : ℕ}
        → (t : OT wₜ (ℕ.suc n))
        → (a : C wₐ)
        → OT (n * wₐ + wₜ) 1
    applyArgTillAlmostFull {0} t a = t
    applyArgTillAlmostFull {ℕ.suc n} {wₜ} {wₐ} t a = 
        let H : n * wₐ + (wₐ + wₜ) ≡ (ℕ.suc n) * wₐ + wₜ
            H = ? -- #TODO: some annoying arithmetic rewriting.
        in
        subst (λ w → OT w 1) H (applyArgTillAlmostFull (giveArg t a) a)
    
    -- But I only care about the special case where wₜ ≡ wₐ ≡ 1...
    -- Well, allowing any wₜ is easier with an inductive definition!
    applyArgTillAlmostFullWeightsOne
        : {n : ℕ}
        → {wₜ : ℕ}
        → (t : OT 1 (ℕ.suc n))
        → (a : C 1)
        → OT (n + wₜ) 1
    applyArgTillAlmostFullWeightsOne {0} t a = ?
    applyArgTillAlmostFullWeightsOne {ℕ.suc n} t a = ?

    

    mkInhabitJumper : InhabitJumper (ClosedTerms {suc∞ μ} {suc∞ ζ} S)
    mkInhabitJumper {w} t = (h , Cw+1+h , intermEmpty)
        where

            -- Term corresponding to the first nullary term, has weight 1.
            -- #TODO: maybe refactor this construction in a separate lemma,
            -- will have more need for it later.
            a₀ : C 1 
            a₀ = subst (λ w → C w) (sucZeroIsOneInℕ μ) (mk-nullary (cardToZero μ))

            -- Arity of the first multiary constructor.
            c₀-ar : ℕ
            c₀-ar = (arity {suc∞ μ} {suc∞ ζ} {S} (cardToZero ζ))

            -- First multiary constructor without arguments applied.
            c₀ : OT 1 c₀-ar
            c₀ = subst (λ w → OT w c₀-ar ) (sucZeroIsOneInℕ ζ) (mk-multiary (cardToZero ζ))

            
            h : ℕ
            h = ?

            Cw+1+h : C (w + 1 + h)
            Cw+1+h = ?

            intermEmpty : ((x : ℕ) → (w < x × x < w + 1 + h) → ¬ C x) 
            intermEmpty x (w<x , x<w+1+h) t = ? -- #TODO: get ⊥


