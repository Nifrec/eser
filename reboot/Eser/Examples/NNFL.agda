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

    private
        C : Set
        C = AllTerms {fin 1} {fin 2} ℤSig

        OT : ℕ → Set
        OT n = Σ[ w ∈ ℕ ] OpenTerms {fin 1} {fin 2} ℤSig w n

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

    θ⁻¹ : C → ℤ'
    θ⁻¹ t = ?

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
    --nf = elift f -- same as:  nf = (ψ ∘ θ) ∘ f ∘ (θ⁻¹ ∘ ψ⁻¹)
    nf = (ψ ∘ θ) ∘ f ∘ (θ⁻¹ ∘ ψ⁻¹)

    -- Only lifting f to act on closed terms of ℤSig.
    nf' : C → C
    nf' = θ ∘ f ∘ θ⁻¹

    -- Smaller-weight-relation.
    infix 4 _<w_
    _<w_ : Rel C 0ℓ
    _<w_ (w , t) (w' , t') = w < w'

    𝐒-monotone : (t t' : C) → t <w t' → 𝐒 t <w 𝐒 t'
    𝐒-monotone t t' t<wt' = ? -- use w < w' -> w+1 < w'+1

    f-weight-decr
        : (z : ℤ')
        → f z ≢ z
        → θ (f z) <w θ z
    f-weight-decr O fz≢z = ⊥-elim $ fz≢z refl
    f-weight-decr (S z) fSz≢Sz = f-weight-decr-Sz (f z) refl
        where
            f-weight-decr-Sz : (z' : ℤ') → (f z ≡ z') → (θ $ f $ S z) <w θ (S z)
            f-weight-decr-Sz O p = subst (λ y → (θ $ f-Sz $ y) <w θ (S z)) (sym p) 
                                         $ 𝐒-monotone (θ O) (θ z) IH
                where
                    H : f z ≢ z
                    H q = ?
                    IH : θ O <w θ z
                    IH = {! f-weight-decr z H !}
            f-weight-decr-Sz (S z') p = {! !}
            f-weight-decr-Sz (P z') p = {! !}

            
    f-weight-decr (P z) fz≢z = {! !}

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

    --nf-fix : (n : ℕ) → nf (nf n) ≡ nf n
    --nf-fix : (n : ℕ) → elift f (elift f n) ≡ elift f n
    --nf-fix = {! ℤ'≃ℕ-lifts.elift-fix f f-fix !}

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
