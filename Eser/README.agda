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
open import Data.Fin hiding (_+_ ; _<_ ; _≤_)
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Data.Sum
open import Data.List using (List ; _∷_ ; [])
open import Function using (_∘_ ; _$_)


module Eser.README where

--------------------------------------------------------------------------------
-- §2 Preliminaries: notation
--------------------------------------------------------------------------------
-- Equivalences
-- _≃_ is defined as _↔_ from the standard library, but I found `_↔_`
-- misleading, it looks more like the weaker condition of functions both ways,
-- and also define it as such in Eser.Aux.
open import Eser.Equivalences.Notation using (_≃_)
open import Eser.Aux using (_↔_)

-- Homotopy
-- f ≈ g if f and g give the same output on each input
-- (for all f , g : A → B, we have f ≈ g iff (a : A) → f a ≡ g a).
open import Eser.Aux using (_≈_)


--------------------------------------------------------------------------------
-- §2 Preliminaries: cardinalities
--------------------------------------------------------------------------------
-- Brief showcase of how we can encode sets of different cartinalities
-- as terms of type ℕ∞.
-- * suc∞ is just ℕ.suc on finite numbers and the identity on ∞
-- * cardToSet c is always a subset of ℕ, so we can inject back into the natural
--      numbers. This is done with `cardToℕ`.
open import Eser.Card using (ℕ∞ ; cardToSet ; suc∞ ; cardToℕ)
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
-- These definitions are defined in Eser.Signature.Definitions.
-- Note that the paper uses _$_ for `giveArg`,
-- but _$_ is in the standard library already defined as function application.

open import Eser.Signature.Definitions
    using
    (Signature
    ; arity
    ; OpenTerms
    ) 
--Signature : ℕ∞ → ℕ∞ → Set
--Signature μ ζ = cardToSet ζ → ℕ

---- Lookup the arity of a constructor in a signature.
--arity : {μ ζ : ℕ∞} → {S : Signature μ ζ} → (c : cardToSet ζ) → ℕ
--arity {S = S} c = ℕ.suc (S c)

---- OpenTerms S w n are the terms over signature S
---- * whose total weight (so far) is w
---- * that still need n more arguments to become a closed term
----      (i.e., to become a constructor with exactly as many inductive
----      arguments as its own arity).
--data OpenTerms {μ ζ : ℕ∞} (S : Signature μ ζ) : ℕ → ℕ → Set where
--    mk-nullary 
--        : (c : cardToSet μ) 
--        → OpenTerms S (ℕ.suc $ cardToℕ c) 0
--    mk-multiary 
--        : (c : cardToSet ζ) 
--        → OpenTerms S (ℕ.suc $ cardToℕ c) (arity {μ} {ζ} {S = S} c)
--    -- Give a closed term as next argument to a strictly open term.
--    giveArg 
--        : {wₜ : ℕ} 
--        → {wₐ : ℕ} 
--        → {m : ℕ} 
--        → (t : OpenTerms {μ} {ζ} S wₜ (ℕ.suc m))
--        → (a : OpenTerms {μ} {ζ} S wₐ 0)
--        → OpenTerms {μ} {ζ} S (wₐ + wₜ) m
    
-- Closed terms: open terms needing no more arguments.
ClosedTerms : {μ ζ : ℕ∞} (S : Signature μ ζ) → ℕ → Set
ClosedTerms {μ} {ζ} S w =  OpenTerms {μ} {ζ} S w 0

-- *All* closed terms over S.
AllTerms : {μ ζ : ℕ∞} (S : Signature μ ζ) → Set
AllTerms {μ} {ζ} S = Σ[ w ∈ ℕ ] (ClosedTerms {μ} {ζ} S w)


-- The OpenTerms defined above are an indexed inductive type,
-- indexed by both the weight and the number of open argument-holes.
-- However, the weights do not constrain the inputs of the constructors,
-- they are mere annotations that can also be computed afterward.
-- For the enumeration proof it is convenient to keep them as indices,
-- but in other places the output type `OpenTerms (wₐ + wₜ) n`
-- of the giveArg constructor (named _$_ in the paper) causes unification
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
        where open import Eser.Signature.MainTheorem using (infTermAlgEnum)


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
        where open import Eser.Signature.PiecewiseFin using (ZTheorem)

    -- Equation (4) in the paper:
    open import Eser.Signature.PiecewiseFin.Definitions {μ} {ζ} S
        using (OT-Nul ; OT-Mul ; OT-Arg)
    OT-decompose
            : (w : ℕ) 
            → (n : ℕ) 
            → OT w n ≃ (OT-Nul w n) ⊎ (OT-Mul w n) ⊎ (OT-Arg w n)
    OT-decompose = ZsubDecompo S
        where open import Eser.Signature.PiecewiseFin using (ZsubDecompo)

    -- Enumerations of OT-Nul, OT-Mul and OT-Arg:
    OT-Nul-Enum : (w n : ℕ) → Σ[ z ∈ ℕ ] (OT-Nul w n ≃ Fin z)
    OT-Nul-Enum = Eq-Nul'
        where 
            open import Eser.Signature.PiecewiseFin.OTNullary S using (Eq-Nul')

    OT-Mul-Enum : (w n : ℕ) → Σ[ z ∈ ℕ ] (OT-Mul w n ≃ Fin z)
    OT-Mul-Enum = Eq-Mul'
        where 
            open import Eser.Signature.PiecewiseFin.OTMultiary S using (Eq-Mul')

    -- There is also a module Eser.Signature.PiecewiseFin.OTGiveArg,
    -- but it is only to be opened in context of a proof by well-founded
    -- induction on (ℕ, <) on weights w : ℕ,
    -- (it is parametrised by a recursive-call-function).
    -- See the implementation of ZTheorem of how it is invoked.

    -- InhabitJumper : 
    -- a function that jumps from one to the next inhabited type
    -- given an ℕ-indexed family of types.
    InhabitJumper : (C : ℕ → Set)  → Set
    InhabitJumper C 
        = {w : ℕ} 
        → C w
        → Σ[ h ∈ ℕ ] (
           --^ Jumping distance (minus one).
           (C $ w + (1 + h)) 
           --^ The destination is inhabited, ...
           × 
           ((x : ℕ) → (w < x × x < w + (1 + h)) → ¬ C x) 
           --^ ... but intermediate points are not.
        )
    -- Proof that all members of a ℕ-indexed family of types are inhabited.
    PiecewiseFin : (P : ℕ → Set) → Set
    PiecewiseFin P = ((w : ℕ) → Σ[ z ∈ ℕ ]( P w ≃ Fin z ))

    lemma-2
        : (PiecewiseFin (ClosedTerms S) )
        -- ^ For every weight w, we know C w ≃ Fin (z w) for some z : ℕ → ℕ.
        → InhabitJumper (ClosedTerms S)
    lemma-2 = mkInhabitJumper {μ'} {ζ'} S
        where
            open import Eser.Signature.JumpEnum using (mkInhabitJumper)

--------------------------------------------------------------------------------
-- Lemma 3 : terms come later in their enumeration than their subterms.
--------------------------------------------------------------------------------
    -- First define the subterm relation on open terms:

    -- This imports the module SubtermDef and the lemma subterm-smaller-weight:
    open import Eser.Signature.Subterm 
    open SubtermDef {μ} {ζ} S using (_⋤_)

    lemma-3
        : {w w' n n' : ℕ}
        → {t : OT w n}
        → {t' : OT w' n'}
        → (t' ⋤ t)
        → w' < w
    lemma-3 = subterm-smaller-weight S

--------------------------------------------------------------------------------
-- §5 Integers
--------------------------------------------------------------------------------
-- These are the same definitions as in Eser.Examples.Integers.Definitions:
open import Eser.Examples.Integers.Definitions using
    ( ℤ' ; O ; S ; P   --^ The grammar z ::= 0 | S z | P z as inductive type.
    ; ℤSig             --^ The grammar z ::= 0 | S z | P z as Signature.
    ; C                --^ All closed terms of ℤSig.
    ; ℤ'≃C 
    ; ℤ'≃ℕ ; θ ; θ⁻¹   --^ The equivalence ℤ' ≃ ℕ with 'to' and 'from' maps.
    -- Definition 6:
    ; IsClean
    ; IsPos
    ; IsNeg
    ; IsZero
    -- Definition 7 (normal form function on ℤ'):
    ; f
    )

lemma-4 : ℤ' ≃ C
lemma-4 = ℤ'≃C

-- First 11 terms of ℤ' in the enumeration ℤ'≃ℕ:
firstElevenTerms : List ℤ'
firstElevenTerms = 
    Data.List.map θ⁻¹ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ [])


opaque
    unfolding  ℤ'≃ℕ

    firstElevenTerms : List ℤ'
    firstElevenTerms = 
        Data.List.map θ⁻¹ (0 ∷ 1 ∷ 2 ∷ 3 ∷ 4 ∷ 5 ∷ 6 ∷ 7 ∷ 8 ∷ 9 ∷ 10 ∷ [])

    firstElevenTermsCheck :
        firstElevenTerms ≡ 
        (  O 
        ∷ (S O) 
        ∷ (S $ S O)
        ∷ (P O)
        ∷ (S $ S $ S O)
        ∷ (S $ P O)
        ∷ (P $ S O)
        ∷ (S $ S $ S $ S O)
        ∷ (S $ S $ P O)
        ∷ (S $ P $ S O)
        ∷ (P $ S $ S O)
        ∷ []
        )
    firstElevenTermsCheck = refl

lemma-5 : (z : ℤ') → (IsClean z) ↔ (f z ≡ z)
lemma-5 z = (f-fixes-on-clean-inp z , 
             λ fz≡z → subst (IsClean) fz≡z (f-cleans z))
    where open import Eser.Examples.Integers.DirectEncProperties
            using (f-fixes-on-clean-inp ; f-cleans)

open import Eser.Examples.Integers using
    ( nf        --^ Lifted version of f, lifted to ℕ → ℕ via ℤ≃ℕ
    ; IsNormal  --^ Defined as: `IsNormal n = (nf n ≡ n)`
    ; ℤ         --^ Actual quotient ℤ ≔ ℤ'≃ℕ / (nf , nf-fix , nf-leq)
    )
lemma-6 : (z : ℤ') → (IsNormal z) ↔ (IsClean z)
lemma-6 z = (cleanIfNormal z , normalIfClean z)
    where 
        open import Eser.Examples.Integers using (cleanIfNormal ; normalIfClean)

lemma-7 : (n : ℕ) → (nf n ≤ n) × (nf (nf n) ≡ nf n)
lemma-7 n = (nf-leq n , nf-fix n)
    where open import Eser.Examples.Integers using (nf-fix ; nf-leq)

open import Data.Integer renaming (ℤ to ℤ#) hiding (_/_)
lemma-8 : ℤ ≃ ℤ#
lemma-8 = ℤcorrectness
    where open import Eser.Examples.Integers using (ℤcorrectness)

--------------------------------------------------------------------------------
-- Addition: defined both on ℤ' and on ℤ.
--------------------------------------------------------------------------------
open import Eser.Examples.Integers.Definitions using (_ℤ'+_)
open import Eser.Examples.Integers using (_ℤ+_)

