-- Module      : Eser.Signature.MainTheorem
-- Description : Main theorem: term algebras over signatures are enumerable.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- "Enumerable" means "equivalent to ⊥, to Fin z (for some z ∈ ℕ) xor to ℕ"

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
open import Eser.Signature.PiecewiseFin
open import Eser.Signature.JumpEnum
open import Eser.Signature.Properties

module Eser.Signature.MainTheorem where

--------------------------------------------------------------------------------
-- Main theorem : all term algebras over these Signatures are enumerable
--
-- Proof strategy:
-- * Show that the inhabited weights, i.e., `Terms w` such that there exists
--      a `t : Terms w`, are all ≃ to `Fin (suc (z w))`
--      for some `(z w) : ℕ`.
--      (This is the hardest part and the only part that I have not entirely
--      worked out all the details on paper, it still requires solving a
--      combinatorial problem. See paper sheet (Lih 7)).
-- * Create a 'jump' function that, given one inhabited weight,
--      outputs the next inhabited weight, plus a proof that all weights
--      inbetween are not inhabited.
-- * To be able to implement this jump function in a terminating way, 
--      define an 'upper bound' function that gives, 
--      for all inhabited weights `w : ℕ`,
--      an `h : ℕ` such that `Terms (w + 1 + h)` is also inhabited
--      (h might not be the minimum, but it allows us to use h as 'fuel'
--      when defining the 'jump' function: it never needs to try more than
--      the first next h weights).
-- * Prove a general theorem that `AllTerms` is _≃_ to the sum over only
--      the weights reached by the jump function.
-- * Prove a general theorem that `Σ[ n ∈ ℕ ] Fin (suc (z n)) ≃ ℕ`.
--------------------------------------------------------------------------------

-- The term algebra of a signature with only nullary constructors
-- is isomorphic to just the set of the nullary constructors.
-- This is either Fin μ (if μ is finite) or ℕ (if μ = ∞).
closedTermAlgEnum
    : {μ : ℕ∞}
    → (S : Signature μ (fin 0))
    → AllTerms {μ} {fin 0} S ≃ cardToSet μ
closedTermAlgEnum = ?

-- The term algebra of a signature without nullary constructors
-- is always empty. There are no atomic terms, and therefore also no arguments
-- to multiary constructors.
emptyTermAlgEmpty
    : {ζ : ℕ∞}
    → (S : Signature (fin 0) ζ )
    → (AllTerms {fin 0} {ζ} S) ≃ ⊥
emptyTermAlgEmpty = ?

-- The term algebra of a signature with at least one nullary constructor a
-- (so an atomic term) and at least one multiarty constructor c
-- is always isomorphic to ℕ, since we can aways construct:
-- t₀ ≔ a
-- t₁ ≔ c(a , ..., a )
-- t₂ ≔ c(t₁, ..., t₂)
-- t₃ ≔ c(t₃, ..., t₃)
-- etc.
infTermAlgEnum
    : {μ ζ : ℕ∞}
    → (S : Signature (suc∞ μ) (suc∞ ζ))
    → (AllTerms {suc∞ μ} {suc∞ ζ} S) ≃ ℕ
--^ See below for the proof

-- Combining the three above lemmas: every term algebra
-- is isomorphic to either `Fin n` for some n ∈ ℕ xor isomorphic to ℕ.
-- That is equivalent to saying, isomorphic to `cardToSet z` for some z ∈ ℕ∞.
everyTermAlgEnum
    : {μ ζ : ℕ∞}
    → (S : Signature μ ζ)
    → Σ[ z ∈ ℕ∞ ](AllTerms {μ} {ζ} S ≃ cardToSet z)
everyTermAlgEnum {μ} 
                 {fin 0} 
                 S = (μ , closedTermAlgEnum {μ} S)
everyTermAlgEnum {fin 0} 
                 {ζ} 
                 S = (fin 0 , emptyTermAlgEmpty {ζ} S)
everyTermAlgEnum {μ@(fin (ℕ.suc x))} 
                 {ζ@(fin (ℕ.suc y))} 
                 S = (∞ , infTermAlgEnum {fin x} {fin y} S)
everyTermAlgEnum {μ@(fin (ℕ.suc x))} 
                 {∞} 
                 S = (∞ , infTermAlgEnum {fin x} {∞} S)
everyTermAlgEnum {∞} 
                 {fin (ℕ.suc y)} 
                 S = (∞ , infTermAlgEnum {∞} {fin y} S)
everyTermAlgEnum {∞} 
                 {∞} 
                 S = (∞ , infTermAlgEnum {∞} {∞} S)
        
--------------------------------------------------------------------------------
-- Big picture proof of infTermAlgEnum
--------------------------------------------------------------------------------

infTermAlgEnum {μ} {ζ} S = 
    --------------------------------------
    -- Unpacking earlier results
    --------------------------------------
    let C = ClosedTerms {suc∞ μ} {suc∞ ζ} S in
    let ¬C0 : C 0 → ⊥ -- All terms have at least weight 1.
        ¬C0 = noWeightlessTerms {suc∞ μ} {suc∞ ζ} S 0
    in
    let J : InhabitJumper C
        J = ?
    in
    -- There is at least one nullary constructor; let a₀ be the corresponding
    -- term. We need a subst to remind Agda that it always has weight 1.
    let a₀ : C 1
        a₀ =
            let H : (ℕ.suc $ cardToℕ $ cardToZero μ) ≡ 1
                H = ?
            in
            subst C H (mk-nullary (cardToZero μ))
    in
    let j : ℕ → ℕ
        j = J-iter {C} 1 a₀ J 
    in
    let zTheoInstance : (w : ℕ) → Σ[ z ∈ ℕ ](C w ≃ Fin z)
        -- Note: we only want closed terms, so always 0 open argument-holes.
        zTheoInstance w = ZTheorem {suc∞ μ} {suc∞ ζ} S w 0
    in
    let jumpTheoInstance 
            : (i : ℕ) → Σ[ z' ∈ ℕ ] (C (J-iter {C} 1 a₀ J i) ≃ Fin (ℕ.suc z'))
        jumpTheoInstance = jumpTheoremInhabitJumper {C} a₀ J zTheoInstance
    in
    let z : ℕ → ℕ
        z i = proj₁ $ jumpTheoInstance i
    in
    let Cw-to-Finz : (i : ℕ) → (C (j i) ≃ (Fin $ ℕ.suc $ z i))
        Cw-to-Finz i = proj₂ $ jumpTheoInstance i
    in
    --------------------------------------
    -- Actual proof: chain of _≃_'s
    --------------------------------------
    begin 
        (Σ[ w ∈ ℕ ] C w)
    -- 1. Filter away uninhabited weights.
    ≃⟨ jumpOver⊥s C J ¬C0 a₀ ⟩
        (Σ[ i ∈ ℕ ] C (j i))
    -- 2. Show every inhabited weight is _≃_ to a nonempty finite set.
    ≃⟨ rewr-≃-rightOf-Σ $ Cw-to-Finz ⟩
        (Σ[ i ∈ ℕ ] (Fin $ ℕ.suc $ z i))
    -- 3. A ℕ-indexed sum of nonempty finite sets is _≃_ to ℕ.
    ≃⟨ Σfin-inf-inhabited z ⟩
        ℕ
    ∎
    

