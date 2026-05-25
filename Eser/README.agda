-- Module      : Eser.README
-- Description : Façade file giving a roadmap to the library
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- This file gives a roadmap of the Eser library following the structure
-- of the paper.

open import Data.Nat hiding (_/_)
open import Data.Empty
open import Data.Fin
open import Relation.Binary.PropositionalEquality
open import Data.Product
open import Data.Sum
open import Function using (_∘_ ; _$_)


module Eser.README where

--------------------------------------------------------------------------------
-- §2 Preliminaries: notation
--------------------------------------------------------------------------------
-- Equivalences
-- _≃_ is defined as _↔_ from the standard library, but I found `_↔_`
-- misleading, it looks more like the weaker condition of functions both ways.
open import Eser.Equivalences.Notation using (_≃_)

-- Homotopy
-- f ≈ g if f and g give the same output on each input
-- (for all f , g : A → B, we have f ≈ g iff (a : A) → f a ≡ g a).
open import Eser.Aux using (_≈_)


--------------------------------------------------------------------------------
-- §2 Preliminaries: cardinalities
--------------------------------------------------------------------------------
-- Brief showcase of how we can encode sets of different cartinalities
-- as terms of type ℕ∞.
-- (suc∞ is just ℕ.suc on finite numbers and the identity on ∞)
open import Eser.Card using (ℕ∞ ; cardToSet ; suc∞)
open ℕ∞ -- Gives constructors `fin : ℕ → ℕ∞` and `∞ : ℕ∞`.

variable 
    n : ℕ

card-example-0 : cardToSet (fin 0) ≡ ⊥
card-example-0 = refl
card-example-Sn : cardToSet (fin (ℕ.suc n)) ≡ Fin (ℕ.suc n)
card-example-Sn = refl
card-example-∞ : cardToSet ∞ ≡ ℕ
card-example-∞ = refl

--------------------------------------------------------------------------------
-- §3.1 Equivalence relations and normal form functions
--------------------------------------------------------------------------------
-- §3.1 is the submodule `Eser.EqRel`.

-- Definitions of decidable equivalence relations and normal-form functions:
open import Eser.EqRel.Definitions using (NFFun) renaming (DecEquiv to EqRel)

-- Conversions between decidable equivalence relations
-- and normal-form functions, named ρ and ρ⁻¹ in the paper:
open import Eser.EqRel.Conversions using () 
    renaming (RelToFun to ρ ; FunToRel to ρ⁻¹)

-- Theorem 1 is split into two lemmas in the implementation:
open import Eser.EqRel.Correspondences using (FRFHomot ; RFRHomot)

theorem-1-part-1 
    : (F : NFFun) 
    → (proj₁ ∘ ρ ∘ ρ⁻¹) F ≈ proj₁ F
theorem-1-part-1 = FRFHomot
-- We uncurry the relation to ℕ × ℕ → Bool to make the homotopy simpler to
-- express.
theorem-1-part-2 
    : (R : EqRel) 
    → (uncurry ∘ proj₁ ∘ ρ⁻¹ ∘ ρ) R ≈ (uncurry ∘  proj₁) R
theorem-1-part-2 = RFRHomot

--------------------------------------------------------------------------------
-- §3.2 Quotients
--------------------------------------------------------------------------------
-- The definition of a quotient is exactly as in the paper:
open import Eser.Quotients using (_/_)
_ : {A : Set} → (A ≃ ℕ) → NFFun → Set
_ = _/_

-- Theorem 2
-- The requires properties and functions related to quotients are in
-- Eser.Quotients.Properties.
-- This module can take a specific equivalence `A ≃ ℕ` as parameter.
open Eser.Quotients.Properties 
    using ([_] ; sound ; emb ; complete ; stable ; effective ; qind)
    renaming (quotLift to lift
             ; deceq to quotients-have-decidable-equalities
             ; ≡-irrel to quotients-have-proof-irrelevant-equalities
             )

--------------------------------------------------------------------------------
-- §4 Singatures
--------------------------------------------------------------------------------
-- The definition of a Signature and the open terms are in
open import Eser.Signature.Definitions 
    using (Signature ; OpenTerms ; ClosedTerms ; AllTerms)
    renaming (mk-nullary to a ; mk-multiary to c ; giveArg to _$'_)
-- (_$_ is in the standard library already defined as function application).
-- (AllTerms is Σ[ w ∈ ℕ ] ClosedTerms w).

-- The OpenTerms defined above are an indexed inductive type,
-- indexed by both the weight and the number of open argument-holes.
-- However, the weights do not constrain the inputs of the constructors,
-- they are mere annotations that can also be computed afterward.
-- For the enumeration proof it is convenient to keep them as indices,
-- but in other places the output type `OpenTerms (wₐ + wₜ) n`
-- of the giveArg constructor (named _$'_ in the paper) causes unification
-- problems since Agda cannot unify an arbitrary `w : ℕ` with `wₐ + wₜ`
-- (since _+_ is a fuction, the type checker doesn't understand every number can
-- be written as a sum of two numbers).
-- So we also define the open terms without weights ('NW ≔ NoWeight').
open import Eser.Signature.NoWeight using (OpenTermsNW)

--------------------------------------------------------------------------------
-- §4.4 Enumeration algorithm
--------------------------------------------------------------------------------
-- Fix a signature with at least one nullary and at least one multiary
-- operation.

module _ {μ' ζ' : ℕ∞} (S : Signature (suc∞ μ') (suc∞ ζ')) where

    μ : ℕ∞
    μ = suc∞ μ'
    ζ : ℕ∞
    ζ = suc∞ ζ'
    OT : ℕ → ℕ → Set
    OT = OpenTerms {μ} {ζ} S

    -- Theorem 3
    theorem-3 : (AllTerms {μ} {ζ} S) ≃ ℕ
    theorem-3 = infTermAlgEnum {μ'} {ζ'} S
        where
            open import Eser.Signature.MainTheorem using (infTermAlgEnum)


    lemma-1
        : (g : ℕ → ℕ)
        → Σ[ i ∈ ℕ ](Fin $ ℕ.suc $ g i) ≃ ℕ
    lemma-1 = Σfin-inf-inhabited
        where
            open import Eser.Equivalences.Properties using (Σfin-inf-inhabited)

    theorem-4
        : (w : ℕ) 
        → (n : ℕ) 
        → Σ[ z ∈ ℕ ]((OpenTerms {μ} {ζ} S w n) ≃ (Fin z))
    theorem-4 = ZTheorem S
        where
            open import Eser.Signature.PiecewiseFin using (ZTheorem)

    -- Equation (4) in the paper:
    open import Eser.Signature.PiecewiseFin.Definitions {μ} {ζ} S
        using (OT-Nul ; OT-Mul ; OT-Arg)
    OT-decompose
            : (w : ℕ) 
            → (n : ℕ) 
            → OT w n ≃ (OT-Nul w n) ⊎ (OT-Mul w n) ⊎ (OT-Arg w n)
    OT-decompose = ZsubDecompo S
        where
            open import Eser.Signature.PiecewiseFin using (ZsubDecompo)

    -- Enumerations of OT-Nul, OT-Mul and OT-Arg:
    OT-Nul-Enum : (w n : ℕ) → Σ[ z ∈ ℕ ] (OT-Nul w n ≃ Fin z)
    OT-Nul-Enum = Eq-Nul'
        where
            open import Eser.Signature.PiecewiseFin.OTNullary S
                using (Eq-Nul')
    OT-Mul-Enum : (w n : ℕ) → Σ[ z ∈ ℕ ] (OT-Mul w n ≃ Fin z)
    OT-Mul-Enum = Eq-Mul'
        where
            open import Eser.Signature.PiecewiseFin.OTMultiary S
                using (Eq-Mul')

    OT-Arg-Enum : (w n : ℕ) → Σ[ z ∈ ℕ ] (OT-Arg w n ≃ Fin z)
    OT-Arg-Enum = WithSignature.AlsoWithW.Z-Eq-Arg
        where
            open import Eser.Signature.PiecewiseFin.OTGiveArg S
                using (Z-Eq-Arg)
