-- Module      : Eser.Examples.NewTheta
-- Description : New implementation for part of Eser.Examples.Integers
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- #TODO: this file is temporary and should be integrated with
-- Eser.Examples.NNFL when done.
--
-- New implementation for θ ℤ' ≃ AllTerms ℤSig
--
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

module Eser.Examples.NewTheta where

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
-- Terms of ℤ' have decidable equality.
--------------------------------------------------------------------------------
S-injective : (z z' : ℤ') → S z ≡ S z' → z ≡ z'
S-injective z z' refl = refl

P-injective : (z z' : ℤ') → P z ≡ P z' → z ≡ z'
P-injective z z' refl = refl

infix 4 _ℤ'≟_
_ℤ'≟_ : (z z' : ℤ') → Dec (z ≡ z')
O ℤ'≟ O = yes refl
O ℤ'≟ S z' = no (λ {()})
O ℤ'≟ P z' = no (λ {()})
S z ℤ'≟ O = no (λ {()})
S z ℤ'≟ S z' with z ℤ'≟ z'
... | yes p = yes (cong S p)
... | no p = no (λ Sz≡Sz' → p $ S-injective z z' Sz≡Sz')
S z ℤ'≟ P z' = no (λ {()})
P z ℤ'≟ O = no (λ {()})
P z ℤ'≟ S z' = no (λ {()})
P z ℤ'≟ P z' with z ℤ'≟ z'
... | yes p = yes (cong P p)
... | no p = no (λ Pz≡Pz' → p $ P-injective z z' Pz≡Pz')

module WithWeights where
    open import Eser.Signature.NoWeight
    open import Eser.Signature.EnumOrderingProperties {fin 0} {fin 1} ℤSig
        using (giveArgBigger)

    private
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
  -- Equivalence between Agda-data-type ℤ' and closed terms over ℤSig 
--------------------------------------------------------------------------------
    𝟎 : CNW
    𝟎 = mk-nullary-nw Fin.zero

    𝐒 : CNW → CNW
    𝐒 a = giveArg-nw (mk-multiary-nw Fin.zero) a

    𝐏 : CNW → CNW
    𝐏 a = giveArg-nw (mk-multiary-nw $ Fin.suc Fin.zero) a

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

    ℤ'≃CNW = mk≃' γ γ⁻¹ invˡ invʳ
        where
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
    
    open ForSignature {fin 0} {fin 1} ℤSig
        hiding (𝕋) -- That's `C` already
        renaming
        (𝕋≃ℕ to C≃ℕ)

    CNW≃C : CNW ≃ C
    CNW≃C = OTequiv {fin 1} {fin 2} ℤSig

    ℤ'≃ℕ : ℤ' ≃ ℕ
    ℤ'≃ℕ = ≃-trans ℤ'≃CNW (≃-trans CNW≃C C≃ℕ)

