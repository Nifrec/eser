-- Module      : Eser.Examples.Integers.Definitions
-- Description : New implementation for part of Eser.Examples.Integers
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
open import Level
open import Data.Nat hiding (_/_)
open import Data.Nat.Properties
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
open import Function
open import Relation.Binary.Reasoning.Syntax
open import Data.Fin.Properties using (fromℕ<-toℕ ; toℕ-fromℕ< ; toℕ-injective)

open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)

open import Eser.Card
open import Eser.Equivalences.Notation
open import Eser.Equivalences.Properties
open import Eser.Aux
open import Eser.Signature
open import Eser.EqRel
open import Eser.Quotient.Definitions

module Eser.Examples.Integers.Definitions where

-- Terms of the grammar z ::= 0 | S z | P z.
--
-- Note: most lemmas we prove about ℤ' come with a dual with S and P exchanged, 
-- whose statements and proofs are otherwise exactly equal.
data ℤ' : Set where
    O : ℤ'
    S : ℤ' → ℤ'
    P : ℤ' → ℤ'

-- Signature representing the inductive type z ::= 0 | S z | P z.
-- One nullary constructor: 0
-- Two 1-ary constructors: S and P
ℤSig : Signature (fin 1) (fin 2)
ℤSig (Fin.zero) = 0                 -- The arity - 1 of S is 0.
ℤSig (Fin.suc Fin.zero) = 0         -- The arity - 1 of P is 0.

ar : Fin 2 → ℕ
ar = arity {fin 1} {fin 2} {ℤSig}


--------------------------------------------------------------------------------
-- Normal-form function on ℤ'
--
-- The stategy is to first define the nf function on ℤ',
-- whose terms have a simple inductive stucture, being an Agda `data` type. 
-- Then we lift this nf function to ℕ via a composition of isomorphisms
-- ℤ' ≃ ClosedTermsNW ℤSig ≃ ClosedTerms ℤSig ≃ ℕ.
--------------------------------------------------------------------------------
-- I implement this function below, but rewrote the `with` clauses
-- into explicit functions to make it easier to prove things about it:
f' : ℤ' → ℤ'
f' O = O
f' (S z) with f' z
... | O = S O
... | S z' = S (S z')
... | P z' = z'
f' (P z) with f' z
... | O = P O
... | S z' = z'
... | P z' = P (P z')

-- First 'with' clause of f, when the input is S z.
f-Sz : ℤ' → ℤ'
f-Sz O = S O
f-Sz (S z') = S (S z')
f-Sz (P z') = z'
-- Second 'with' clause of f, when the input is P z.
f-Pz : ℤ' → ℤ'
f-Pz O = P O
f-Pz (S z') = z'
f-Pz (P z') = P (P z')
-- Actual top-level function.
f : ℤ' → ℤ'
f O = O
f (S z) = f-Sz (f z)
f (P z) = f-Pz (f z)

--------------------------------------------------------------------------------
-- IsClean predicate on ℤ'
--
-- A term is 'clean' if it does not contain both an S and a P.
-- These terms are exactly the normal forms according to f,
-- i.e., fixed points of f 
-- (see Eser.Examples.Integers.DirectEncProperties for the proof they are).
--------------------------------------------------------------------------------

IsZero : ℤ' → Set
IsZero O = ⊤
IsZero (S z) = ⊥
IsZero (P z) = ⊥

IsPos : ℤ' → Set
IsPos O = ⊥
IsPos (S O) = ⊤
IsPos (S (S z)) = IsPos (S z)
IsPos (S (P z)) = ⊥
IsPos (P z) = ⊥

IsNeg : ℤ' → Set
IsNeg O = ⊥
IsNeg (S z) = ⊥
IsNeg (P O) = ⊤
IsNeg (P (P z)) = IsNeg (P z)
IsNeg (P (S z)) = ⊥

IsClean : ℤ' → Set
IsClean z = IsZero z ⊎ IsPos z ⊎ IsNeg z

--------------------------------------------------------------------------------
-- Weight-annotated terms over ℤSig, normal-form function on them
--------------------------------------------------------------------------------

-- Closed and open terms of ℤSig with weights as indices.
-- For these closed terms we have a "≃ ℕ" proof.
C : Set
C = AllTerms {fin 1} {fin 2} ℤSig

OT : ℕ → ℕ → Set
OT w n = OpenTerms {fin 1} {fin 2} ℤSig w n


-- Closed and open terms of ℤSig without weight indices.
-- For these closed terms we have no direct "≃ ℕ" proof,
-- but we use the composition CWN ≃ C ≃ ℕ.
CNW : Set
CNW = ClosedTermsNW {fin 1} {fin 2} ℤSig

OTNW : ℕ  → Set
OTNW n = OpenTermsNW {fin 1} {fin 2} ℤSig n

--------------------------------------------------------------------------------
-- Equivalences
--------------------------------------------------------------------------------
-- This module gives definitions based on the 'NoWeights' representation
-- of open terms over ℤSig.
module WithoutWeights where
    open import Eser.Signature.NoWeight
    open import Eser.Signature.EnumOrderingProperties {fin 0} {fin 1} ℤSig
        using (giveArgBigger)

    𝟎 : CNW
    𝟎 = mk-nullary-nw Fin.zero

    𝐒 : CNW → CNW
    𝐒 a = giveArg-nw (mk-multiary-nw Fin.zero) a

    𝐏 : CNW → CNW
    𝐏 a = giveArg-nw (mk-multiary-nw $ Fin.suc Fin.zero) a

--------------------------------------------------------------------------------
  -- Equivalence between Agda-data-type ℤ' and closed terms over ℤSig 
--------------------------------------------------------------------------------

    γ : ℤ' → CNW
    γ O = 𝟎
    γ (S t) = 𝐒 (γ t)
    γ (P t) = 𝐏 (γ t)


    -- This lemma is very specific for ℤSig: it has only 0- and 1-ary
    -- constructors.
    aritiesAtMost1
        : {c : Fin 2}
        → 2 ≤ ar c
        → ⊥
    aritiesAtMost1 {Fin.zero} (s≤s ())
    aritiesAtMost1 {Fin.suc Fin.zero} (s≤s ())

    OTNW-n≥2-empty : (n : ℕ) → (2 ≤ n) → OTNW n → ⊥
    OTNW-n≥2-empty 0 p (mk-nullary-nw c) = 1+n≰n (≤-trans p (z≤n {1}))
    OTNW-n≥2-empty n p (mk-multiary-nw c) = aritiesAtMost1 p
    OTNW-n≥2-empty n p (giveArg-nw t a) =
        -- t has 1+n hols and 2 ≤ n implies also 2 ≤ 1+n; so recurse on t.
        OTNW-n≥2-empty (ℕ.suc n) (≤-trans p (n≤1+n n)) t

    OTNW-2-empty : {n : ℕ} → n ≡ 1 → OTNW (ℕ.suc n) → ⊥
    OTNW-2-empty p t = OTNW-n≥2-empty 2 (≤-refl) 
                                    $ subst (λ y → OTNW (ℕ.suc y)) p t

    γ⁻¹lemma : {n : ℕ} → OTNW n → n ≡ 1 → ℤ' → ℤ'
    γ⁻¹lemma (mk-multiary-nw Fin.zero) p = S
    γ⁻¹lemma (mk-multiary-nw (Fin.suc Fin.zero)) p = P
    γ⁻¹lemma (giveArg-nw t' a') p = ⊥-elim contra
        where
            contra : ⊥
            contra = OTNW-2-empty p t'

    γ⁻¹ : CNW → ℤ'
    γ⁻¹ (mk-nullary-nw Fin.zero) = O
    γ⁻¹ (giveArg-nw t a) = γ⁻¹lemma {1} t refl (γ⁻¹ a)


    invˡ : Inverseˡ _≡_ _≡_ γ γ⁻¹
    invˡ {mk-nullary-nw Fin.zero} {y} refl = refl
    invˡ {giveArg-nw t a} {y} refl = 
        ≡begin 
            (γ $ γ⁻¹ $ giveArg-nw t a)
        ≡⟨⟩ -- Unfold definition of γ⁻¹ one step.
            γ (γ⁻¹lemma {1} t refl (γ⁻¹ a))
        ≡⟨  γγ⁻¹-lemma {1} t refl (γ⁻¹ a) ⟩
            giveArg-nw (subst OTNW refl t) (γ $ γ⁻¹ a)
        ≡⟨⟩ -- subst normalises on input refl.
            giveArg-nw t (γ $ γ⁻¹ a)
            -- Apply IH to rewrite γ (γ⁻¹ a) ≡ a
        ≡⟨ cong (giveArg-nw t) $ invˡ refl ⟩ 
            giveArg-nw t a
        ≡∎
        where
            γγ⁻¹-lemma
                : {n : ℕ} 
                → (t : OTNW n)
                → (p : n ≡ 1)
                → (z : ℤ')
                → γ (γ⁻¹lemma {n} t p z) ≡ giveArg-nw (subst OTNW p t) (γ z)
            γγ⁻¹-lemma {n} (mk-multiary-nw Fin.zero) refl z = 
                -- Note: every step is a judgemental equality (i.e., refl).
                ≡begin 
                    γ (γ⁻¹lemma (mk-multiary-nw Fin.zero) refl z)
                ≡⟨⟩
                    γ (S z)
                ≡⟨⟩
                    𝐒 (γ z)
                ≡⟨⟩
                    giveArg-nw (mk-multiary-nw Fin.zero) (γ z)
                ≡⟨⟩
                    giveArg-nw (subst OTNW refl (mk-multiary-nw Fin.zero)) 
                               (γ z)
                ≡∎
            -- Same as above but with Fin.suc Fin.zero instead of Fin.zero. 
            γγ⁻¹-lemma {n} (mk-multiary-nw (Fin.suc Fin.zero)) refl z = refl
            γγ⁻¹-lemma {n} (giveArg-nw t a) p z = ⊥-elim $ OTNW-2-empty p t

    invʳ : Inverseʳ _≡_ _≡_ γ γ⁻¹
    invʳ {O} {x} refl = refl
    invʳ {S y} {x} refl = 
        ≡begin 
           (γ⁻¹ $ γ $ S y)
        ≡⟨⟩
           (γ⁻¹ $ 𝐒 $ γ y)
        ≡⟨⟩
           (S $ γ⁻¹ $ γ y)
        ≡⟨ cong S (invʳ refl) ⟩
            S y 
        ≡∎
    -- Same as above, but with P i.o. S. 
    invʳ {P y} {x} refl = cong P (invʳ refl)

opaque

    open ForSignature {fin 0} {fin 1} ℤSig using (𝕋≃ℕ) 
    C≃ℕ : C ≃ ℕ
    C≃ℕ = 𝕋≃ℕ 
    φ : C → ℕ
    φ = ≃-to C≃ℕ
    φ⁻¹ : ℕ → C
    φ⁻¹ = ≃-from C≃ℕ
    φ∘φ⁻¹≈id : (φ ∘ φ⁻¹) ≈ id
    φ∘φ⁻¹≈id = ≃-toFrom C≃ℕ
    φ⁻¹∘φ≈id : (φ⁻¹ ∘ φ) ≈ id
    φ⁻¹∘φ≈id = ≃-fromTo C≃ℕ

    CNW≃C : CNW ≃ C
    CNW≃C = OTequiv {fin 1} {fin 2} ℤSig 0

    ℤ'≃CNW : ℤ' ≃ CNW 
    ℤ'≃CNW = mk≃' γ γ⁻¹ invˡ invʳ
        where 
            open WithoutWeights

    ℤ'≃C : ℤ' ≃ C
    ℤ'≃C = (≃-trans ℤ'≃CNW CNW≃C)
    ψ : ℤ' → C
    ψ = ≃-to ℤ'≃C
    ψ⁻¹ : C → ℤ'
    ψ⁻¹ = ≃-from ℤ'≃C
    ψ∘ψ⁻¹≈id : (ψ ∘ ψ⁻¹) ≈ id
    ψ∘ψ⁻¹≈id = ≃-toFrom ℤ'≃C
    ψ⁻¹∘ψ≈id : (ψ⁻¹ ∘ ψ) ≈ id
    ψ⁻¹∘ψ≈id = ≃-fromTo ℤ'≃C

    ℤ'≃ℕ : ℤ' ≃ ℕ
    ℤ'≃ℕ = ≃-trans ℤ'≃C C≃ℕ

    open Elift {ℤ'} {ℕ} ℤ'≃ℕ public 
        using (elift ; elift-fix)
        renaming
        (φ to θ
        ;φ⁻¹ to θ⁻¹
        ;φ∘φ⁻¹≈id to θ∘θ⁻¹≈id
        ;φ⁻¹∘φ≈id to θ⁻¹∘θ≈id
        )
     
--------------------------------------------------------------------------------
-- Normal form function on ℤ' to ℕ.
--------------------------------------------------------------------------------

-- Lifting f to the ℕ-encoding of ℤ' terms.
nf : ℕ → ℕ
nf = elift f

nf-def : nf ≡ elift f
nf-def = refl

-- Only lifting f to act on closed terms of ℤSig.
nf' : C → C
nf' = ψ ∘ f ∘ ψ⁻¹


