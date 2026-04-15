-- Module      : Eser.Signature.PiecewiseFin
-- Description : Proof that `OpenTerms w n ≃ Fin z` for some z, for all w n : ℕ.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- Intermediate result towards proving that all term algebras of signatures
-- are enumerable: showing that every set open terms of a given weight
-- and a given number of still-required-arguments
-- is isomorphic to some finite set.
--
-- Strategy:
-- 1. OT 0 n ≃ Fin 0 since there are terms of weight 0.
-- 2. for w = suc ŵ:
--  OT w n ≡ (OT-Nul w n) ⊎ (OT-Mul w n) ⊎ (OT-Arg w n)
--      where 
--          OT-Nul w n are the terms in OT w n made with mk-nullary.
--          OT⁼ w n are the terms in OT w n made with mk-multiary,
--              i.e., constructors without any aguments applied.
--          OT-Arg w n are the terms in OT w n made with giveArg,
--              i.e., constructors with one or more arguments applied.
-- 3. OT-Nul w (suc n) ≃ Fin 0 always, 
--      because nullary constructors don't need arguments. 
--    OT-Nul w 0 ≃ Fin 1 if there are at least w nullary constructors,
--      and OT-Nul w 0 ≃ ⊥ otherwise; 
--      only the term with index w-1 has weight w,
--      but it doesn't exist if the set of nullary constructors
--      is smaller than Fin w.
-- 3. OT-Mul w n ≃ Fin 1 if there are at least w constructors
--      and the constructor with index w-1 has arity n.
--      Otherwise OT-Mul w n ≃ Fin 0
-- 4. showing OT-Arg w n ≃ Fin (ż-Arg w n) is the only hard case.
--      How many open terms of the form `giveArg t a`
--      of weight w needing n more arguments exist?
--      Well note the following data is required to build such a term:
--          - weights wₜ and wₐ such that wₐ + wₜ ≡ w.
--              There are w-1 = ŵ such choices (see point 6 below).
--          - A base term t ∈ OT wₜ (suc n) ≃ Fin(ż wₜ n)
--          - An argument a ∈ OT wₐ 0       ≃ Fin(ż wₐ 0)
--      The last two equivalences can be obtained via Well-Founded (ℕ, <)
--      recursion on w when defining the ZTheoremInhab via <-rec;
--      the reasoning is as follows:
--      since both weights are inhabited we must have wₜ ≥ 1 and wₐ ≥ 1, 
--      so if w ≡ wₐ + wₜ then both wₐ < w and wₜ < w must hold. 
--      Consequently, we can make recursive calls with arguments wₐ and wₜ.
-- 5. So define 
--  OT-Arg w n ≔ Σ[(wₜ,wₐ,p) ∈ Splits w](OT wₜ (suc n)) × (OT wₐ 0)
--          ≃ Σ[Fin( ŵ )] Fin(ż wₜ n) × Fin(ż wₐ 0)
-- 6. Here `Splits w` (for any w ≗ suc ŵ) is the set of splits of w into 
--      two non-zero numbers that sum to w.
--      Formally:
--          Splits w ≔ Σ[x ∈ ℕ]Σ[y ∈ ℕ](suc x + suc y ≡ w)
--      Note that x ∈ {0, ..., w-2} ≃ Fin w-1 ≃ Fin ŵ,
--      and choosing an x fixes the only
--      possible choice of y already as 
--          suc y ≡ w - suc x = ŵ - x
--              so
--          y ≡ ŵ - x - 1
--      which has exactly one solution for all x ∈ {0, ..., ŵ-1},
--      if ŵ ≥ 1 and none if ŵ ≡ 0, but then x ∈ ⊥ anyway.
--      Hence the solutions are in bijection to the choice of x ∈ Fin ŵ.

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

open import Eser.Aux
open import Eser.Card
open import Eser.Equivalences.Notation
open import Eser.Equivalences.Properties
open import Eser.Signature.Definitions
open import Eser.Signature.Properties
open import Eser.Signature.Splits

module Eser.Signature.PiecewiseFin where

open import Eser.Signature.PiecewiseFin.Definitions using (ZP)

--------------------------------------------------------------------------------
-- Theorem: there are finitely many terms of a fixed weight
--
-- I.e., `OpenTerms w n ≃ Fin (z n w)` for all w ∈ ℕ for some z : ℕ → ℕ → ℕ
--------------------------------------------------------------------------------
 
-- Implementation of the proof for the ZTheorem for the case where w ≥ 1.
-- Submodule that also assumes a given weight w and num-remaining-args n
-- plus the ability to perfrom Well-Founded recursion on w.
module WithArgs
    {μ ζ : ℕ∞}
    (S : Signature μ ζ)
    (w-1 : ℕ)
    (rec : {w' : ℕ} → (w' < ℕ.suc w-1) → ZP {μ} {ζ} S w')
    (n : ℕ) 
    where
    open import Eser.Signature.PiecewiseFin.OTNullary {μ} {ζ} S
    open import Eser.Signature.PiecewiseFin.OTMultiary {μ} {ζ} S
    open import Eser.Signature.PiecewiseFin.OTGiveArg
    open Eser.Signature.PiecewiseFin.OTGiveArg.WithSignature.AlsoWithW-1&Rec&N 
        {μ} {ζ} S w-1 rec n hiding (w)
    open Eser.Signature.PiecewiseFin.Definitions {μ} {ζ} S

    -- Trivial sublemma: OT w n is an Agda-inductive type, and hence the sum
    -- over all of its Agda-constructors of the subsets of the terms
    -- constructed with that constructor.
    ZsubDecompo 
        : (w : ℕ) 
        → (n : ℕ) 
        → OT w n ≃ (OT-Nul w n) ⊎ (OT-Mul w n) ⊎ (OT-Arg w n)
    ZsubDecompo w n = mk≃ {to = to} {from = from} inv
        where 
            to : OT w n → (OT-Nul w n) ⊎ (OT-Mul w n) ⊎ (OT-Arg w n)
            to t@(mk-nullary _) = inj₁ (t , tt)
            to t@(mk-multiary _) = inj₂ $ inj₁ (t , tt)
            to t@(giveArg _ _) = inj₂ $ inj₂ (t , tt)

            from : (OT-Nul w n) ⊎ (OT-Mul w n) ⊎ (OT-Arg w n) → OT w n
            from (inj₁ (t , _)) = t
            from (inj₂ (inj₁ (t , _))) = t
            from (inj₂ (inj₂ (t , _))) = t
            invˡ : Inverseˡ _≡_ _≡_ to from
            invˡ {inj₁ (mk-nullary _ , tt)} {t} refl = refl
            invˡ {inj₂ (inj₁ (mk-multiary _ , tt))} {t} refl = refl
            invˡ {inj₂ (inj₂ (giveArg _ _ , tt))} {t} refl = refl
            invʳ : Inverseʳ _≡_ _≡_ to from
            invʳ {mk-nullary _} {x} refl = refl
            invʳ {mk-multiary _} {x} refl = refl
            invʳ {giveArg _ _} {x} refl = refl
            inv : Inverseᵇ _≡_ _≡_ to from
            inv = (invˡ , invʳ)

    w = ℕ.suc w-1
    Z-Nul : ℕ
    Z-Nul = proj₁ $ Eq-Nul' w n
    Eq-Nul : OT-Nul w n ≃ Fin Z-Nul
    Eq-Nul = proj₂ $ Eq-Nul' w n 

    Z-Mul : ℕ
    Z-Mul = proj₁ $ Eq-Mul' w n
    Eq-Mul : OT-Mul w n ≃ Fin Z-Mul
    Eq-Mul = proj₂ $ Eq-Mul' w n
        
    Z-Arg : ℕ
    Z-Arg = proj₁ Z-Eq-Arg
    Eq-Arg : OT-Arg w n ≃ Fin Z-Arg
    Eq-Arg = proj₂ Z-Eq-Arg

    z : ℕ
    z = Z-Nul + Z-Mul + Z-Arg

    zEquiv : OT w n ≃ Fin z
    zEquiv =
        begin 
            OT w n
        ≃⟨ ZsubDecompo w n ⟩
            ((OT-Nul w n) ⊎ (OT-Mul w n) ⊎ (OT-Arg w n))
        ≃⟨ rewr-≃-under-⊎-3 Eq-Nul Eq-Mul Eq-Arg ⟩
            (Fin Z-Nul ⊎ Fin Z-Mul ⊎ Fin Z-Arg)
        ≃⟨ rewr-≃-under-⊎-right (fin-⊎-+ Z-Mul Z-Arg) ⟩
            (Fin Z-Nul ⊎ Fin (Z-Mul + Z-Arg ))
        ≃⟨ fin-⊎-+ Z-Nul (Z-Mul + Z-Arg) ⟩
            Fin (Z-Nul + (Z-Mul + Z-Arg))
        ≃⟨ fin-+-assoc Z-Nul Z-Mul Z-Arg ⟩
            Fin (Z-Nul + Z-Mul + Z-Arg)
        ≃⟨ ≃-refl ⟩
            Fin z
        ∎

openTermsWeightless≃Fin0
    : {μ ζ : ℕ∞} 
    → (S : Signature μ ζ)
    → (n : ℕ)
    → OpenTerms {μ} {ζ} S 0 n ≃ Fin 0
-- #TODO: almost same proof occurs in Eq-Nul' and Eq-Mul' in the w ≗ cases.
-- This redundancy can probably be avoided?
openTermsWeightless≃Fin0 {μ} {ζ} S n = ≃-trans equiv (≃-sym fin0)
        where
            OT = OpenTerms {μ} {ζ} S
            equiv : OT 0 n ≃ ⊥
            equiv = mk≃' f f⁻¹ invˡ invʳ
                where
                f : OT 0 n → ⊥
                f t = noWeightlessTerms S n t
                f⁻¹ : ⊥ → OT 0 n
                f⁻¹ ()
                invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
                invˡ {()} {t}
                invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
                invʳ {t} {()}


-- The main statement is as follows:
ZTheorem 
    : {μ ζ : ℕ∞} 
    → (S : Signature μ ζ)
    → (w : ℕ) 
    → (n : ℕ) 
    → Σ[ z ∈ ℕ ]((OpenTerms {μ} {ζ} S w n) ≃ (Fin z))
ZTheorem {μ} {ζ} S w = <-rec (ZP S) f w
    where
        f : (w : ℕ) → (rec : {w' : ℕ} → w' < w → ZP {μ} {ζ} S w') → ZP {μ} {ζ} S w
        f 0 _ = λ n → (0 , openTermsWeightless≃Fin0 {μ} {ζ} S n)
        f (suc w') rec n = (z , zEquiv)
            where
                z = WithArgs.z {μ} {ζ} S w' rec n
                zEquiv = WithArgs.zEquiv {μ} {ζ} S w' rec n

-- Alternative presentation of the ZTheorem: give the sizes of the finite
-- sets as a function z : (w : ℕ) → (n : ℕ) → (<size of OT w n> : ℕ).
-- (The ZTheorem uses WF < recursion on w, so it's more convenient to take w as
-- argument there, rather than nesting it below the Σ[ z ∈ ... ] ...).
Z   : {μ ζ : ℕ∞} 
    → (S : Signature (μ) (ζ))
    → Σ[ z ∈ (ℕ → ℕ → ℕ) ](
        (w : ℕ) → (n : ℕ) → ((OpenTerms {μ} {ζ} S w n) ≃ (Fin $ z w n)))
Z {μ} {ζ} S = (z , p)
    where
        z = λ w → λ n → proj₁ (ZTheorem {μ} {ζ} S w n)
        p = λ w → λ n → proj₂ (ZTheorem {μ} {ζ} S w n)

