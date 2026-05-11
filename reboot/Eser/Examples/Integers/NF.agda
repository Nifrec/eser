-- Module      : Eser.Examples.Integers.NF
-- Description : Normal-form properties of the `nf` function.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- Proofs that the normal form function satisfies, for all n : ℕ:
-- nf-leq : nf n ≤ n
-- nf-fix : nf (nf n) ≡ nf n
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

open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)

open import Eser.Card
open import Eser.Equivalences.Notation
open import Eser.Equivalences.Properties
open import Eser.Aux
open import Eser.Signature
open import Eser.Examples.Integers.Definitions
open import Eser.Examples.Integers.DirectEncProperties

module Eser.Examples.Integers.NF where

-- This proof uses the weight-annotated representation of open terms over ℤSig.
open Eser.Examples.Integers.Definitions.WithWeights

open import Eser.Signature.EnumOrderingProperties {fin 0} {fin 1} ℤSig
    using (giveArgBigger)

get𝐒𝐏-lemma
    : (wₐ : ℕ)
    → (a : OT wₐ 0)
    → (c : Fin 2)
    → (proj₁ $ get𝐒𝐏 c (wₐ , a)) ≡ wₐ + (ℕ.suc $ cardToℕ c)
get𝐒𝐏-lemma wₐ a (Fin.zero) = refl
get𝐒𝐏-lemma wₐ a (Fin.suc Fin.zero) = refl

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
-- ψ (f z) ≡ ψ z' <w ψ (P z') <w ψ (S P z') ≡ ψ (S z)
-- since both 𝐒 and 𝐏 are <w-decreasing (and 𝐏 ψ z' ≗ ψ P z').
--
-- If f z ≢ z, then we can make a recursive call (induction hypothesis IH)
-- giving us that ψ (f z) <w ψ z (*).
-- Then pattern-match on f z, which simplifies both the LHS of (*)
-- as well as the goal (since the output of f (S z) ≗ f-Sz (f z)
-- computes when we match f z). 
-- Each of the cases f z ∈ {O , S z' , P z'} then follows from the IH,
-- 𝐒-<w-monoticity and <w-increasingness of 𝐏 and 𝐒.
f-weight-decr
    : (z : ℤ')
    → f z ≢ z
    → ψ (f z) <w ψ z
f-weight-decr O fz≢z = ⊥-elim $ fz≢z refl
f-weight-decr (S z) fSz≢Sz = case-Sz ((f z) ℤ'≟ z)
    where
        case-Sz : Dec (f z ≡ z) → (ψ $ f $ S z) <w ψ (S z)
        case-Sz-fz≢z 
            : (f z ≢ z) 
            → (z' : ℤ') 
            → (f z ≡ z') 
            → (ψ $ f $ S z) <w ψ (S z)
        case-Sz-fz≡z : f z ≡ z → (ψ $ f $ S z) <w ψ (S z)

        case-Sz (yes fz≡z) = case-Sz-fz≡z fz≡z
        case-Sz (no fz≢z) = case-Sz-fz≢z fz≢z (f z) refl

        case-Sz-fz≡z fz≡z = H₄
            where
                z' : ℤ'
                z' = proj₁ $ z-must-be-Pz' z fSz≢Sz fz≡z
                z≡Pz' : z ≡ P z'
                z≡Pz' = proj₂ $ z-must-be-Pz' z fSz≢Sz fz≡z

                H₁ : ψ z' <w ψ (P z')
                H₁ = 𝐏-<w-intro (ψ z')

                H₂ : ψ z' <w ψ (S (P z') )
                H₂ = 𝐒-<w-increasing (ψ z') (ψ (P z')) H₁

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

                H₃ : ψ z' <w ψ (S z)
                H₃ = subst (λ y → ψ z' <w ψ (S y)) (sym z≡Pz') H₂

                H₄ : ψ (f (S z)) <w ψ (S z)
                H₄ = subst (λ y → ψ y <w ψ (S z)) K H₃
        case-Sz-fz≢z H O p = subst (λ y → (ψ $ f-Sz $ y) <w ψ (S z)) (sym p) 
                                     $ 𝐒-monotone (ψ O) (ψ z) IH
            where
                IH : ψ O <w ψ z
                IH = subst (λ y → ψ y <w ψ z) p $ f-weight-decr z H
        case-Sz-fz≢z H (S z') p = subst (λ y → (ψ $ y) <w (ψ $ S z)) H₂ H₁
            where
                IH : ψ (S z') <w ψ z
                IH = subst (λ y → ψ y <w ψ z) p $ f-weight-decr z H

                H₁ : (ψ $ S $ S z') <w (ψ $ S z)
                H₁ = 𝐒-monotone (ψ $ S z') (ψ z) IH

                H₂ : S (S z') ≡ f (S z)
                -- LHS is same as: f-Sz (S z')
                -- RHS is same as: f-Sz (f z)
                H₂ = cong f-Sz $ sym p
        case-Sz-fz≢z H (P z') p = ans
            where
                IH : ψ (P z') <w ψ z
                IH = subst (λ y → ψ y <w ψ z) p $ f-weight-decr z H

                K : ψ z' <w ψ (S z)
                K = <w-trans (ψ z') (ψ $ P z') (ψ $ S z)
                    (𝐏-<w-intro (ψ z'))
                    (<w-trans (ψ $ P z') (ψ z) (ψ $ S z) IH (𝐒-<w-intro (ψ z)))

                ans : (ψ $ f $ S z) <w (ψ $ S z)
                ans = subst (λ y → (ψ $ f-Sz y) <w (ψ $ S z)) (sym p) K
-- Proof for the `P z` case is litterally same as for the `S z` case,
-- only with P and S, and 𝐏 and 𝐒, exchanged.
f-weight-decr (P z) fPz≢Pz = case-Pz ((f z) ℤ'≟ z)
    where
        case-Pz : Dec (f z ≡ z) → (ψ $ f $ P z) <w ψ (P z)
        case-Pz-fz≢z 
            : (f z ≢ z) 
            → (z' : ℤ') 
            → (f z ≡ z') 
            → (ψ $ f $ P z) <w ψ (P z)
        case-Pz-fz≡z : f z ≡ z → (ψ $ f $ P z) <w ψ (P z)

        case-Pz (yes fz≡z) = case-Pz-fz≡z fz≡z
        case-Pz (no fz≢z) = case-Pz-fz≢z fz≢z (f z) refl

        case-Pz-fz≡z fz≡z = H₄
            where
                z' : ℤ'
                z' = proj₁ $ z-must-be-Sz' z fPz≢Pz fz≡z
                z≡Sz' : z ≡ S z'
                z≡Sz' = proj₂ $ z-must-be-Sz' z fPz≢Pz fz≡z

                H₁ : ψ z' <w ψ (S z')
                H₁ = 𝐒-<w-intro (ψ z')

                H₂ : ψ z' <w ψ (P (S z') )
                H₂ = 𝐏-<w-increasing (ψ z') (ψ (S z')) H₁

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

                H₃ : ψ z' <w ψ (P z)
                H₃ = subst (λ y → ψ z' <w ψ (P y)) (sym z≡Sz') H₂

                H₄ : ψ (f (P z)) <w ψ (P z)
                H₄ = subst (λ y → ψ y <w ψ (P z)) K H₃
        case-Pz-fz≢z H O p = subst (λ y → (ψ $ f-Pz $ y) <w ψ (P z)) (sym p) 
                                     $ 𝐏-monotone (ψ O) (ψ z) IH
            where
                IH : ψ O <w ψ z
                IH = subst (λ y → ψ y <w ψ z) p $ f-weight-decr z H
        case-Pz-fz≢z H (P z') p = subst (λ y → (ψ $ y) <w (ψ $ P z)) H₂ H₁
            where
                IH : ψ (P z') <w ψ z
                IH = subst (λ y → ψ y <w ψ z) p $ f-weight-decr z H

                H₁ : (ψ $ P $ P z') <w (ψ $ P z)
                H₁ = 𝐏-monotone (ψ $ P z') (ψ z) IH

                H₂ : P (P z') ≡ f (P z)
                -- LHP is same as: f-Pz (P z')
                -- RHP is same as: f-Pz (f z)
                H₂ = cong f-Pz $ sym p
        case-Pz-fz≢z H (S z') p = ans
            where
                IH : ψ (S z') <w ψ z
                IH = subst (λ y → ψ y <w ψ z) p $ f-weight-decr z H

                K : ψ z' <w ψ (P z)
                K = <w-trans (ψ z') (ψ $ S z') (ψ $ P z)
                    (𝐒-<w-intro (ψ z'))
                    (<w-trans (ψ $ S z') (ψ z) (ψ $ P z) IH (𝐏-<w-intro (ψ z)))

                ans : (ψ $ f $ P z) <w (ψ $ P z)
                ans = subst (λ y → (ψ $ f-Pz y) <w (ψ $ P z)) (sym p) K

-- Normalisation (on the closed-terms-ofℤSig-representation)
-- either returns the input xor returns something of smaller weight.
-- Smaller weight is a stronger condition 
-- than smaller enumeration-number (= smaller φ-image) !!!
nf'-weight-decr
    : (t : C)
    → nf' t ≢ t
    → nf' t <w t
nf'-weight-decr t H = subst (λ y → nf' t <w y) (ψ∘ψ⁻¹≈id t) H''
    where
        z : ℤ'
        z = ψ⁻¹ t

        H' : f z ≢ z
        H' p = H (subst (λ y → (ψ ∘ f) z ≡ y) (ψ∘ψ⁻¹≈id t) (cong ψ p))

        H'' : nf' t <w ψ (ψ⁻¹ t)
        H'' = f-weight-decr (ψ⁻¹ t) H'

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
                wₐ = proj₁ $ nf' $ φ⁻¹ n
                a  : ClosedTerms ℤSig wₐ
                a  = proj₂ $ nf' $ φ⁻¹ n
                wₓ : ℕ
                wₓ = proj₁ $ φ⁻¹ n
                x  : ClosedTerms ℤSig wₓ
                x  = proj₂ $ φ⁻¹ n
                -- Rewrite nf n ≢ n   to   nf n ≢ φ ∘ φ⁻¹ n
                nfn≢φφ⁻¹n : nf n ≢ (φ ∘ φ⁻¹) n
                nfn≢φφ⁻¹n nfn≡φφ⁻¹n = nfn≢n H
                    where
                        H : nf n ≡ n
                        H = subst (λ y → nf n ≡ y) (φ∘φ⁻¹≈id n) nfn≡φφ⁻¹n

                nf'φ⁻¹n≢φ⁻¹n : (nf' $ φ⁻¹ n) ≢ (φ⁻¹ n)
                nf'φ⁻¹n≢φ⁻¹n p = H $ cong φ p
                    where
                        H : (φ ∘ nf' ∘ φ⁻¹) n ≢ (φ ∘ φ⁻¹) n
                        -- This uses a definitional equality: nf ≗ φ∘nf∘φ⁻¹
                        H = nfn≢φφ⁻¹n

                nf'n<φφ⁻¹n : nf n < (φ ∘ φ⁻¹) n
                nf'n<φφ⁻¹n = smallerWeightSmallerIdx {wₐ} {wₓ} a x 
                             (nf'-weight-decr (φ⁻¹ n) nf'φ⁻¹n≢φ⁻¹n)
                ans : nf n < n
                ans  = subst (λ y → nf n < y) (φ∘φ⁻¹≈id n) nf'n<φφ⁻¹n

module ℤ'≃ℕ-lifts = Elift {ℤ'} ℤ'≃ℕ
nf-fix : (n : ℕ) → elift f (elift f n) ≡ elift f n
nf-fix = ℤ'≃ℕ-lifts.elift-fix f f-fix
