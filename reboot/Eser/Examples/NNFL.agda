-- Module      : Eser.Examples.NNFL
-- Description : New implementation for part of Eser.Examples.Integers
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- #TODO: this file is temporary and should be integrated with
-- Eser.Examples.Integers when done.
--
-- Content: "New NF-Leq"-proof showing that the normal-form function for
-- integers satisfies nf n ℕ≤ n.
-- We have equivalences
-- (ℤ') --θ-> (AllTerms ℤSig) --ψ-> (ℕ)
-- 
--
-- This proof does not make use of the _⊑_ order on ℤ',
-- but instead proves that normalisation of a ℤ'-term either
-- (1) Outputs the input unchanged.
-- xor
-- (2) Outputs a term whose θ-image has a strictly smaller weight than the
--      input.
-- This works because normalisation removes `SP` and `PS` substrings,
-- each of which contributes weight 3 to the term.
-- So the (θ-image of the) output of `nf n` has a weight equal to the weight of
-- `n` minus a multiple of 3.
--
-- The previous approach with _⊑_ ran into problems, as it required comparing
-- terms of equal weight, but my implementation makes it rather difficult
-- to prove anything about how terms *within* `ClosedTerms ℤSig w`
-- are enumerated (terms with the same weight w ∈ ℕ in mean).
-- Proving that terms with a smaller weight have a smaller ψ-image is easy
-- though, and that we are exploiting in the current implementation.
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

module Eser.Examples.NNFL where

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


--------------------------------------------------------------------------------
-- Normal-form function
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

module IsCleanPredicates where
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

    f-Sz-presv-cleanness
        : (z : ℤ')
        → IsClean z
        → IsClean (f-Sz z)
    f-Sz-presv-cleanness O (inj₁ tt) = inj₂ $ inj₁ tt
    f-Sz-presv-cleanness O (inj₂ (inj₁ ()))
    f-Sz-presv-cleanness O (inj₂ (inj₂ ()))
    f-Sz-presv-cleanness (S O) (inj₂ (inj₁ tt)) = inj₂ $ inj₁ tt
    f-Sz-presv-cleanness (S (S z)) (inj₂ (inj₁ x)) = inj₂ $ inj₁ x
    f-Sz-presv-cleanness (P O) (inj₂ (inj₂ tt)) = inj₁ tt
    f-Sz-presv-cleanness (P (P z)) (inj₂ (inj₂ y)) = inj₂ $ inj₂ y

    f-Pz-presv-cleanness
        : (z : ℤ')
        → IsClean z
        → IsClean (f-Pz z)
    f-Pz-presv-cleanness O (inj₁ tt) = inj₂ $ inj₂ tt
    f-Pz-presv-cleanness O (inj₂ (inj₁ ()))
    f-Pz-presv-cleanness O (inj₂ (inj₂ ()))
    f-Pz-presv-cleanness (P O) (inj₂ (inj₂ tt)) = inj₂ $ inj₂ tt
    f-Pz-presv-cleanness (P (P z)) (inj₂ (inj₂ x)) = inj₂ $ inj₂ x
    f-Pz-presv-cleanness (S O) (inj₂ (inj₁ tt)) = inj₁ tt
    f-Pz-presv-cleanness (S (S z)) (inj₂ (inj₁ y)) = inj₂ $ inj₁ y

    is-clean-S-downgrade
        : {z : ℤ'}
        → IsClean (S z)
        → IsClean z
    is-clean-S-downgrade {O} k@(inj₂ (inj₁ tt)) = inj₁ tt
    is-clean-S-downgrade {S z} k@(inj₂ (inj₁ x)) = k

    is-clean-P-downgrade
        : {z : ℤ'}
        → IsClean (P z)
        → IsClean z
    is-clean-P-downgrade {O} k@(inj₂ (inj₂ tt)) = inj₁ tt
    is-clean-P-downgrade {P z} k@(inj₂ (inj₂ x)) = k

    f-presv-cleanness 
        : (z : ℤ')
        → IsClean z
        → IsClean (f z)
    f-presv-cleanness O (inj₁ tt) = inj₁ tt
    f-presv-cleanness O (inj₂ (inj₁ ()))
    f-presv-cleanness O (inj₂ (inj₂ ()))
    f-presv-cleanness (S z) k@(inj₂ (inj₁ x)) = 
        f-Sz-presv-cleanness (f z) IH
        where
            IH : IsClean (f z)
            IH = f-presv-cleanness z (is-clean-S-downgrade k)
    f-presv-cleanness (P z) k@(inj₂ (inj₂ x)) = 
        f-Pz-presv-cleanness (f z) IH
        where
            IH : IsClean (f z)
            IH = f-presv-cleanness z (is-clean-P-downgrade k)

    f-cleans : (z : ℤ') → IsClean (f z)
    f-cleans O = inj₁ tt
    f-cleans (S z) = f-Sz-presv-cleanness (f z) IH
        where 
            IH : IsClean (f z)
            IH = f-cleans z
    f-cleans (P z) = f-Pz-presv-cleanness (f z) IH
        where 
            IH : IsClean (f z)
            IH = f-cleans z

open IsCleanPredicates

f-fixes-on-clean-inp : (z : ℤ') → IsClean z → f z ≡ z
f-fixes-on-clean-inp O k = refl
f-fixes-on-clean-inp (S O) (inj₂ (inj₁ tt)) = refl
f-fixes-on-clean-inp (S (S z)) k@(inj₂ (inj₁ x)) = 
    ≡begin 
        f (S (S z))
    ≡⟨⟩
        f-Sz (f (S z))
    ≡⟨ cong f-Sz $ f-fixes-on-clean-inp (S z) (is-clean-S-downgrade {S z} k) ⟩
        f-Sz (S z)
    ≡⟨⟩
        S (S z)
    ≡∎
f-fixes-on-clean-inp (P O) (inj₂ (inj₂ tt)) = refl
f-fixes-on-clean-inp (P (P z)) k@(inj₂ (inj₂ x)) =
    ≡begin 
        f (P (P z))
    ≡⟨⟩
        f-Pz (f (P z))
    ≡⟨ cong f-Pz $ f-fixes-on-clean-inp (P z) (is-clean-P-downgrade {P z} k) ⟩
        f-Pz (P z)
    ≡⟨⟩
        P (P z)
    ≡∎

f-fix : (z : ℤ') → f (f z) ≡ f z
f-fix z = f-fixes-on-clean-inp (f z) (f-cleans z)

module WithWeights where
    open import Eser.Signature.EnumOrderingProperties {fin 0} {fin 1} ℤSig
        using (giveArgBigger)

    private
        C : Set
        C = AllTerms {fin 1} {fin 2} ℤSig

        OT : ℕ → ℕ → Set
        OT w n = OpenTerms {fin 1} {fin 2} ℤSig w n

    open ForSignature {fin 0} {fin 1} ℤSig
        hiding (𝕋) -- That's `C` already
        renaming
        (𝕋≃ℕ to C≃ℕ)
    ----------------------------------------------------------------------------
    -- Equivalence between Agda-data-type ℤ' and closed terms over ℤSig
    ----------------------------------------------------------------------------
    𝟎 : C
    𝟎 = (1 , mk-nullary Fin.zero)

    𝐒 : C → C
    𝐒 (wₐ , a) = (wₐ + 1 , giveArg (mk-multiary Fin.zero) a)

    𝐏 : C → C
    𝐏 (wₐ , a) = (wₐ + 2 , giveArg (mk-multiary $ Fin.suc Fin.zero) a)

    θ : ℤ' → C
    θ O = 𝟎
    θ (S t) = 𝐒 (θ t)
    θ (P t) = 𝐏 (θ t)

    OT-decompose
        : (w : ℕ)
        → (t : OT w 1)
        → (Σ[ H ∈ 1 ≡ w ] t ≡ subst (λ w → OT w 1) H (mk-multiary Fin.zero)) 
          ⊎ 
          (Σ[ H ∈ 2 ≡ w ] t ≡ subst (λ w → OT w 1) H (mk-multiary $ Fin.suc Fin.zero)) 
    OT-decompose w t = ?

    θ⁻¹ : C → ℤ'
    θ⁻¹ (w , mk-nullary Fin.zero) = O
    θ⁻¹ (w , giveArg {wₜ} {wₐ} t a) = (caseDistinction wₜ t) (θ⁻¹ (wₐ , a))
        where
            caseDistinction
                : (w : ℕ)
                → (t : OT w 1)
                → ℤ' 
                → ℤ'
            caseDistinction w t = ?

    ℤ'≃C : ℤ' ≃ C
    ℤ'≃C = mk≃' θ θ⁻¹ invˡ invʳ
        where
        invˡ : Inverseˡ _≡_ _≡_ θ θ⁻¹
        invˡ {x} {y} refl = ?
        invʳ : Inverseʳ _≡_ _≡_ θ θ⁻¹
        invʳ {y} {x} refl = ?
    
    θ∘θ⁻¹≈id : (θ ∘ θ⁻¹) ≈ id {_} {C}
    θ∘θ⁻¹≈id = ≃-toFrom ℤ'≃C

    open EquivShorthandsForEnumSet C≃ℕ
        renaming
        ( φ to ψ
        ; φ⁻¹ to ψ⁻¹
        ; φ∘φ⁻¹≈id to ψ∘ψ⁻¹≈id
        ; φ⁻¹∘φ≈id to ψ⁻¹∘ψ≈id
        ; _«_ to _C«_
        ; _«=_ to _C«=_
        )

    ℤ'≃ℕ : ℤ' ≃ ℕ
    ℤ'≃ℕ = ≃-trans ℤ'≃C C≃ℕ
    open EquivShorthands ℤ'≃ℕ 

    -- Check if ≃-trans indeed gives our composition:
    check : φ ≡ ψ ∘ θ
    check = refl

    check⁻¹ : φ⁻¹ ≡ θ⁻¹ ∘ ψ⁻¹
    check⁻¹ = refl

    -- Lifting f to the ℕ-encoding of ℤ' terms.
    nf : ℕ → ℕ
    nf = elift f -- same as:  nf = (ψ ∘ θ) ∘ f ∘ (θ⁻¹ ∘ ψ⁻¹)
    -- nf = (ψ ∘ θ) ∘ f ∘ (θ⁻¹ ∘ ψ⁻¹)

    -- Only lifting f to act on closed terms of ℤSig.
    nf' : C → C
    nf' = θ ∘ f ∘ θ⁻¹

    -- Smaller-weight-relation.
    infix 4 _<w_
    _<w_ : Rel C 0ℓ
    _<w_ (w , t) (w' , t') = w < w'

    𝐒-monotone : (t t' : C) → t <w t' → 𝐒 t <w 𝐒 t'
    𝐒-monotone t t' t<wt' = +-monoˡ-< 1 t<wt'

    𝐏-monotone : (t t' : C) → t <w t' → 𝐏 t <w 𝐏 t'
    𝐏-monotone t t' t<wt' = +-monoˡ-< 2 t<wt'

    <w-trans : (t₁ t₂ t₃ : C) → t₁ <w t₂ → t₂ <w t₃ → t₁ <w t₃
    <w-trans t₁ t₂ t₃ H K = <-trans H K

    𝐒-<w-intro : (t : C) → t <w 𝐒 t
    𝐒-<w-intro (wₜ , t) = n<n+1 wₜ

    𝐒-<w-increasing : (t t' : C) → t <w t' → t <w 𝐒 t'
    𝐒-<w-increasing t t' H = <w-trans t (𝐒 t) (𝐒 t') (𝐒-<w-intro t) 
                                                     (𝐒-monotone t t' H)

    𝐏-<w-intro : (t : C) → t <w 𝐏 t
    𝐏-<w-intro (wₜ , t) = n<n+Sm wₜ 1 -- Note that: 2 ≗ suc 1

    𝐏-<w-increasing : (t t' : C) → t <w t' → t <w 𝐏 t'
    𝐏-<w-increasing t t' H = <w-trans t (𝐏 t) (𝐏 t') (𝐏-<w-intro t) 
                                                     (𝐏-monotone t t' H)

    -- #TODO: unused, maybe remove, or move elsewhere.
    f-pos-fixpoint
        : (z : ℤ')
        → f (S z) ≡ S z
        → IsZero z ⊎ IsPos z
    f-pos-fixpoint z H = caseDistinction z Sz-is-clean
        where
            Sz-is-clean : IsClean (S z)
            Sz-is-clean = subst (λ y → IsClean y) H (f-cleans $ S z)

            caseDistinction : (z : ℤ') → IsClean (S z) → IsZero z ⊎ IsPos z
            caseDistinction O (inj₂ (inj₁ x)) = inj₁ tt
            caseDistinction (S O) (inj₂ (inj₁ x)) = inj₂ tt
            caseDistinction (S (S z)) (inj₂ (inj₁ x)) = inj₂ x

    -- If f (S z) ≢ S z   and   f z ≡ z
    -- Then
    -- (1) z must be clean, otherwise it is not a fixpoint of f.
    -- (2) if z ≡ O, then f (S O) = S O, contradiction.
    -- (3) if z ≡ S z', then z only has Ss and f (S z) ≡ S z, contradiction.
    -- (4) so we must have z ≡ P z'.
    z-must-be-Pz'
        : (z : ℤ')
        → (f (S z) ≢ S z)
        → f z ≡ z
        → Σ[ z' ∈ ℤ' ](z ≡ P z')
    z-must-be-Pz' O H _ = ⊥-elim (H refl) -- f O ≡ O always holds.
    z-must-be-Pz' (S z) fSSz≢SSz fSz≡Sz = ⊥-elim $ fSSz≢SSz fSSz≡SSz
        where
            SSz-clean : IsClean $ S (S z)
            SSz-clean = subst (λ y → IsClean y) (fSz≡Sz) (f-cleans $ S z)
            fSSz≡SSz : (f $ S $ S z) ≡ (S $ S z)
            fSSz≡SSz = f-fixes-on-clean-inp (S (S z)) SSz-clean
    z-must-be-Pz' (P z) _ _ = (z , refl)

    -- Same as above under P<->S exchange.
    z-must-be-Sz'
        : (z : ℤ')
        → (f (P z) ≢ P z)
        → f z ≡ z
        → Σ[ z' ∈ ℤ' ](z ≡ S z')
    z-must-be-Sz' O H _ = ⊥-elim (H refl)
    z-must-be-Sz' (P z) fPPz≢PPz fPz≡Pz = ⊥-elim $ fPPz≢PPz fPPz≡PPz
        where
            PPz-clean : IsClean $ P (P z)
            PPz-clean = subst (λ y → IsClean y) (fPz≡Pz) (f-cleans $ P z)
            fPPz≡PPz : (f $ P $ P z) ≡ (P $ P z)
            fPPz≡PPz = f-fixes-on-clean-inp (P (P z)) PPz-clean
    z-must-be-Sz' (S z) _ _ = (z , refl)

    -- Implementation discussion of f-weight-decr:
    -- This proof makes a lot of nested case distinctions.
    -- First match the input z. z ≗ O gives a contradiction
    -- with f O ≢ O, so w.l.o.g. assume the input to be `S z`
    -- (the case `P z` is symmetric).
    --
    -- Now, f (S z) ≢ (S z) does NOT imply that f z ≢ z.
    -- In particular, f (S P O) ≡ O ≢ S P O while f (P O) ≡ P O.
    -- But equalities in ℤ' are decidable so make a case distinction
    -- on f z ≟ z.
    --
    -- If f z ≡ z, then that combined with f (S z) ≢ S z
    -- implies that z ≡ P z' for some z' (see z-must-be-Pz' above),
    -- and then f z ≡ z'. 
    -- So we conclude 
    -- θ (f z) ≡ θ z' <w θ (P z') <w θ (S P z') ≡ θ (S z)
    -- since both 𝐒 and 𝐏 are <w-decreasing (and 𝐏 θ z' ≗ θ P z').
    --
    -- If f z ≢ z, then we can make a recursive call (induction hypothesis IH)
    -- giving us that θ (f z) <w θ z (*).
    -- Then pattern-match on f z, which simplifies both the LHS of (*)
    -- as well as the goal (since the output of f (S z) ≗ f-Sz (f z)
    -- computes when we match f z). 
    -- Each of the cases f z ∈ {O , S z' , P z'} then follows from the IH,
    -- 𝐒-<w-monoticity and <w-increasingness of 𝐏 and 𝐒.
    f-weight-decr
        : (z : ℤ')
        → f z ≢ z
        → θ (f z) <w θ z
    f-weight-decr O fz≢z = ⊥-elim $ fz≢z refl
    f-weight-decr (S z) fSz≢Sz = case-Sz ((f z) ℤ'≟ z)
        where
            case-Sz : Dec (f z ≡ z) → (θ $ f $ S z) <w θ (S z)
            case-Sz-fz≢z 
                : (f z ≢ z) 
                → (z' : ℤ') 
                → (f z ≡ z') 
                → (θ $ f $ S z) <w θ (S z)
            case-Sz-fz≡z : f z ≡ z → (θ $ f $ S z) <w θ (S z)

            case-Sz (yes fz≡z) = case-Sz-fz≡z fz≡z
            case-Sz (no fz≢z) = case-Sz-fz≢z fz≢z (f z) refl

            case-Sz-fz≡z fz≡z = H₄
                where
                    z' : ℤ'
                    z' = proj₁ $ z-must-be-Pz' z fSz≢Sz fz≡z
                    z≡Pz' : z ≡ P z'
                    z≡Pz' = proj₂ $ z-must-be-Pz' z fSz≢Sz fz≡z

                    H₁ : θ z' <w θ (P z')
                    H₁ = 𝐏-<w-intro (θ z')

                    H₂ : θ z' <w θ (S (P z') )
                    H₂ = 𝐒-<w-increasing (θ z') (θ (P z')) H₁

                    K : z' ≡ f (S z)
                    K = ≡begin 
                            z'
                        ≡⟨⟩
                            (f-Sz $ P z')
                        ≡⟨  cong f-Sz $ sym $ trans fz≡z z≡Pz' ⟩
                            (f-Sz $ f z)
                        ≡⟨⟩
                            f (S z)
                        ≡∎

                    H₃ : θ z' <w θ (S z)
                    H₃ = subst (λ y → θ z' <w θ (S y)) (sym z≡Pz') H₂

                    H₄ : θ (f (S z)) <w θ (S z)
                    H₄ = subst (λ y → θ y <w θ (S z)) K H₃
            case-Sz-fz≢z H O p = subst (λ y → (θ $ f-Sz $ y) <w θ (S z)) (sym p) 
                                         $ 𝐒-monotone (θ O) (θ z) IH
                where
                    IH : θ O <w θ z
                    IH = subst (λ y → θ y <w θ z) p $ f-weight-decr z H
            case-Sz-fz≢z H (S z') p = subst (λ y → (θ $ y) <w (θ $ S z)) H₂ H₁
                where
                    IH : θ (S z') <w θ z
                    IH = subst (λ y → θ y <w θ z) p $ f-weight-decr z H

                    H₁ : (θ $ S $ S z') <w (θ $ S z)
                    H₁ = 𝐒-monotone (θ $ S z') (θ z) IH

                    H₂ : S (S z') ≡ f (S z)
                    -- LHS is same as: f-Sz (S z')
                    -- RHS is same as: f-Sz (f z)
                    H₂ = cong f-Sz $ sym p
            case-Sz-fz≢z H (P z') p = ans
                where
                    IH : θ (P z') <w θ z
                    IH = subst (λ y → θ y <w θ z) p $ f-weight-decr z H

                    K : θ z' <w θ (S z)
                    K = <w-trans (θ z') (θ $ P z') (θ $ S z)
                        (𝐏-<w-intro (θ z'))
                        (<w-trans (θ $ P z') (θ z) (θ $ S z) IH (𝐒-<w-intro (θ z)))

                    ans : (θ $ f $ S z) <w (θ $ S z)
                    ans = subst (λ y → (θ $ f-Sz y) <w (θ $ S z)) (sym p) K
    -- Proof for the `P z` case is litterally same as for the `S z` case,
    -- only with P and S, and 𝐏 and 𝐒, exchanged.
    f-weight-decr (P z) fPz≢Pz = case-Pz ((f z) ℤ'≟ z)
        where
            case-Pz : Dec (f z ≡ z) → (θ $ f $ P z) <w θ (P z)
            case-Pz-fz≢z 
                : (f z ≢ z) 
                → (z' : ℤ') 
                → (f z ≡ z') 
                → (θ $ f $ P z) <w θ (P z)
            case-Pz-fz≡z : f z ≡ z → (θ $ f $ P z) <w θ (P z)

            case-Pz (yes fz≡z) = case-Pz-fz≡z fz≡z
            case-Pz (no fz≢z) = case-Pz-fz≢z fz≢z (f z) refl

            case-Pz-fz≡z fz≡z = H₄
                where
                    z' : ℤ'
                    z' = proj₁ $ z-must-be-Sz' z fPz≢Pz fz≡z
                    z≡Sz' : z ≡ S z'
                    z≡Sz' = proj₂ $ z-must-be-Sz' z fPz≢Pz fz≡z

                    H₁ : θ z' <w θ (S z')
                    H₁ = 𝐒-<w-intro (θ z')

                    H₂ : θ z' <w θ (P (S z') )
                    H₂ = 𝐏-<w-increasing (θ z') (θ (S z')) H₁

                    K : z' ≡ f (P z)
                    K = ≡begin 
                            z'
                        ≡⟨⟩
                            (f-Pz $ S z')
                        ≡⟨  cong f-Pz $ sym $ trans fz≡z z≡Sz' ⟩
                            (f-Pz $ f z)
                        ≡⟨⟩
                            f (P z)
                        ≡∎

                    H₃ : θ z' <w θ (P z)
                    H₃ = subst (λ y → θ z' <w θ (P y)) (sym z≡Sz') H₂

                    H₄ : θ (f (P z)) <w θ (P z)
                    H₄ = subst (λ y → θ y <w θ (P z)) K H₃
            case-Pz-fz≢z H O p = subst (λ y → (θ $ f-Pz $ y) <w θ (P z)) (sym p) 
                                         $ 𝐏-monotone (θ O) (θ z) IH
                where
                    IH : θ O <w θ z
                    IH = subst (λ y → θ y <w θ z) p $ f-weight-decr z H
            case-Pz-fz≢z H (P z') p = subst (λ y → (θ $ y) <w (θ $ P z)) H₂ H₁
                where
                    IH : θ (P z') <w θ z
                    IH = subst (λ y → θ y <w θ z) p $ f-weight-decr z H

                    H₁ : (θ $ P $ P z') <w (θ $ P z)
                    H₁ = 𝐏-monotone (θ $ P z') (θ z) IH

                    H₂ : P (P z') ≡ f (P z)
                    -- LHP is same as: f-Pz (P z')
                    -- RHP is same as: f-Pz (f z)
                    H₂ = cong f-Pz $ sym p
            case-Pz-fz≢z H (S z') p = ans
                where
                    IH : θ (S z') <w θ z
                    IH = subst (λ y → θ y <w θ z) p $ f-weight-decr z H

                    K : θ z' <w θ (P z)
                    K = <w-trans (θ z') (θ $ S z') (θ $ P z)
                        (𝐒-<w-intro (θ z'))
                        (<w-trans (θ $ S z') (θ z) (θ $ P z) IH (𝐏-<w-intro (θ z)))

                    ans : (θ $ f $ P z) <w (θ $ P z)
                    ans = subst (λ y → (θ $ f-Pz y) <w (θ $ P z)) (sym p) K


    -- Normalisation (on the closed-terms-ofℤSig-representation)
    -- either returns the input xor returns something of smaller weight.
    -- Smaller weight is a stronger condition 
    -- than smaller enumeration-number (= smaller ψ-image) !!!
    nf'-weight-decr
        : (t : C)
        → nf' t ≢ t
        → nf' t <w t
    nf'-weight-decr t H = subst (λ y → nf' t <w y) (θ∘θ⁻¹≈id t) H''
        where
            z : ℤ'
            z = θ⁻¹ t

            H' : f z ≢ z
            H' p = H (subst (λ y → (θ ∘ f) z ≡ y) (θ∘θ⁻¹≈id t) (cong θ p))

            H'' : nf' t <w θ (θ⁻¹ t)
            H'' = f-weight-decr (θ⁻¹ t) H'

    open import Eser.Signature.EnumOrderingProperties {fin 0} {fin 1} ℤSig
        using (smallerWeightSmallerIdx)

    nf-leq : (n : ℕ) → nf n Data.Nat.≤ n 
    nf-leq n = nf-leq-sublemma (nf n Data.Nat.≟ n)
        where
            nf-leq-sublemma : Dec (nf n ≡ n) → nf n ≤ n
            -- Matching p with `refl` made the type checker loop here
            -- (run forever, run out of memory, etc.).
            -- So use the lemma that n ≡ m → n ≤ m, which type checks quickly.
            nf-leq-sublemma (yes p) = ≡→≤ p
            nf-leq-sublemma (no nfn≢n) = <⇒≤ ans
                where
                    wₐ : ℕ
                    wₐ = proj₁ $ nf' $ ψ⁻¹ n
                    a  : ClosedTerms ℤSig wₐ
                    a  = proj₂ $ nf' $ ψ⁻¹ n
                    wₓ : ℕ
                    wₓ = proj₁ $ ψ⁻¹ n
                    x  : ClosedTerms ℤSig wₓ
                    x  = proj₂ $ ψ⁻¹ n
                    -- Rewrite nf n ≢ n   to   nf n ≢ ψ ∘ ψ⁻¹ n
                    nfn≢ψψ⁻¹n : nf n ≢ (ψ ∘ ψ⁻¹) n
                    nfn≢ψψ⁻¹n nfn≡ψψ⁻¹n = nfn≢n H
                        where
                            H : nf n ≡ n
                            H = subst (λ y → nf n ≡ y) (ψ∘ψ⁻¹≈id n) nfn≡ψψ⁻¹n

                    nf'ψ⁻¹n≢ψ⁻¹n : (nf' $ ψ⁻¹ n) ≢ (ψ⁻¹ n)
                    nf'ψ⁻¹n≢ψ⁻¹n p = H $ cong ψ p
                        where
                            H : (ψ ∘ nf' ∘ ψ⁻¹) n ≢ (ψ ∘ ψ⁻¹) n
                            -- This uses a definitional equality: nf ≗ ψ∘nf∘ψ⁻¹
                            H = nfn≢ψψ⁻¹n

                    nf'n<ψψ⁻¹n : nf n < (ψ ∘ ψ⁻¹) n
                    nf'n<ψψ⁻¹n = smallerWeightSmallerIdx {wₐ} {wₓ} a x 
                                 (nf'-weight-decr (ψ⁻¹ n) nf'ψ⁻¹n≢ψ⁻¹n)
                    ans : nf n < n
                    ans  = subst (λ y → nf n < y) (ψ∘ψ⁻¹≈id n) nf'n<ψψ⁻¹n

    module ℤ'≃ℕ-lifts = Elift {ℤ'} ℤ'≃ℕ
    -- nf-fix : (n : ℕ) → nf (nf n) ≡ nf n
    nf-fix : (n : ℕ) → elift f (elift f n) ≡ elift f n
    nf-fix = {! ℤ'≃ℕ-lifts.elift-fix f f-fix !}

--------------------------------------------------------------------------------
-- Proof that ℤ are indeed the integers
--
-- In particular, we show that our quotient type ℤ is equivalent
-- to the definition of integers used in the standard library.
-- The standard library defines integers as the inductive type
-- with constructors:
--      pos      : ℕ → ℤ
--      negsuc   : ℕ → ℤ
-- with the interpretation that:
--      pos n    = + n
--      negsuc n = - (n+1)
-- (This interpretation avoids having distinct +0 and -0.
--------------------------------------------------------------------------------
import Data.Integer
module StdlibInt = Data.Integer

ℤ : Set
ℤ = ?

ℤcorrectness : ℤ ≃ StdlibInt.ℤ
ℤcorrectness = ?

-- #EXT: Add addition?
