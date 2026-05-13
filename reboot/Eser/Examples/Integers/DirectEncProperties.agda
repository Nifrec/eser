-- Module      : Eser.Examples.Integers.DirectEncProperties
-- Description : Properties of the Agda datatype ℤ' ::= 0 | S z | P z
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
open import Eser.Examples.Integers.Definitions

module Eser.Examples.Integers.DirectEncProperties where

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
-- Properties related to f and the IsClean predicate.
--
-- In particular, it follows that `IsClean z` iff `z` is a fixpoint of `f`,
-- i.e., a normal form.
--------------------------------------------------------------------------------


opaque
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


--------------------------------------------------------------------------------
-- Properties used in the ℤCorrectness theorem in Examples.Eser.Integer.
--------------------------------------------------------------------------------

-- Compute absolute value of an integer (using the ℤ' representation of
-- integers).
abs : (z : ℤ') → IsClean z → ℕ
abs O     p@(inj₁ isZero)       = 0
abs O     p@(inj₂ (inj₁ ()))
abs O     p@(inj₂ (inj₂ ()))
abs (S z) p@(inj₂ (inj₁ isPos)) = ℕ.suc (abs z $ is-clean-S-downgrade {z} p)
abs (P z) p@(inj₂ (inj₂ isNeg)) = ℕ.suc (abs z $ is-clean-P-downgrade {z} p)

-- Make a ℤ' term as a tower of n times `S` applied to O.
S-stack : ℕ → ℤ'
S-stack 0 = O
S-stack (suc n) = S (S-stack n)
P-stack : ℕ → ℤ'
P-stack 0 = O
P-stack (suc n) = P (P-stack n)

opaque

    S-stack-isPos : (n : ℕ) → IsPos (S-stack $ ℕ.suc n)
    S-stack-isPos ℕ.zero = tt
    S-stack-isPos (ℕ.suc n) = S-stack-isPos n

    P-stack-isNeg : (n : ℕ) → IsNeg (P-stack $ ℕ.suc n)
    P-stack-isNeg ℕ.zero = tt
    P-stack-isNeg (ℕ.suc n) = P-stack-isNeg n

    -- If z is positive then there exist a clean z' s.t. z ≡ S z'.
    -- (z' might not be positive, it can also be O).
    isPos-to-predec'
        : (z : ℤ')
        → (p : IsPos z)
        → Σ[ z' ∈ ℤ' ] (IsClean z') × (
            Σ[ k ∈ z ≡ S z' ] (
                _≡_ {A = Σ[ z ∈ ℤ' ] IsClean z}
                    (z , inj₂ (inj₁ p)) 
                    (S z' , (inj₂  (inj₁ $ subst (λ x → IsPos x) k p)))
            )
        )
    isPos-to-predec' (S O) tt = (O , inj₁ tt , refl , refl)
    isPos-to-predec' (S (S z)) p = 
        (S z 
        , is-clean-S-downgrade {S z} (inj₂ $ inj₁ p)
        , refl
        , refl
        )
    -- If z is negative then there exist a clean z' s.t. z ≡ P z'.
    -- (z' might not be negative, it can also be O).
    isNeg-to-predec'
        : (z : ℤ')
        → (p : IsNeg z)
        → Σ[ z' ∈ ℤ' ] (IsClean z') × (
            Σ[ k ∈ z ≡ P z' ] (
                _≡_ {A = Σ[ z ∈ ℤ' ] IsClean z}
                    (z , inj₂ (inj₂ p)) 
                    (P z' , (inj₂  (inj₂ $ subst (λ x → IsNeg x) k p)))
            )
        )
    isNeg-to-predec' (P O) tt = (O , inj₁ tt , refl , refl)
    isNeg-to-predec' (P (P z)) p = 
        (P z 
        , is-clean-P-downgrade {P z} (inj₂ $ inj₂ p)
        , refl
        , refl
        )

    isPosIrrel : (z : ℤ') → Relation.Nullary.Irrelevant (IsPos z)
    isPosIrrel (S O) tt tt = refl
    isPosIrrel (S (S z)) p q = isPosIrrel (S z) p q

    isNegIrrel : (z : ℤ') → Relation.Nullary.Irrelevant (IsNeg z)
    isNegIrrel (P O) tt tt = refl
    isNegIrrel (P (P z)) p q = isNegIrrel (P z) p q

    isCleanIrrel : (z : ℤ') → Relation.Nullary.Irrelevant (IsClean z)
    isCleanIrrel O (inj₁ tt) (inj₁ tt) = refl
    isCleanIrrel O (inj₁ p') (inj₂ (inj₁ ()))
    isCleanIrrel O (inj₁ p') (inj₂ (inj₂ ()))
    isCleanIrrel O (inj₂ (inj₁ ())) 
    isCleanIrrel O (inj₂ (inj₂ ()))
    isCleanIrrel (S z) (inj₂ (inj₁ p')) (inj₂ (inj₁ q')) = cong (inj₂ ∘ inj₁) p'≡q'
        where
            p'≡q' : p' ≡ q'
            p'≡q' = isPosIrrel (S z) p' q'
    isCleanIrrel (P z) (inj₂ (inj₂ p')) (inj₂ (inj₂ q')) = cong (inj₂ ∘ inj₂) p'≡q'
        where
            p'≡q' : p' ≡ q'
            p'≡q' = isNegIrrel (P z) p' q'

    is-clean-S-downgrade-nonneg
        : (z : ℤ')
        → (p : IsClean (S z))
        → IsZero z ⊎ IsPos z
    is-clean-S-downgrade-nonneg O (inj₂ (inj₁ tt)) = inj₁ tt
    is-clean-S-downgrade-nonneg (S z) (inj₂ (inj₁ p)) = inj₂ p
    is-clean-S-downgrade-nonneg (P z) (inj₂ (inj₁ ()))
    is-clean-S-downgrade-nonneg (P z) (inj₂ (inj₂ ()))

    is-clean-P-downgrade-nonpos
        : (z : ℤ')
        → (p : IsClean (P z))
        → IsZero z ⊎ IsNeg z
    is-clean-P-downgrade-nonpos O (inj₂ (inj₂ tt)) = inj₁ tt
    is-clean-P-downgrade-nonpos (S z) (inj₂ (inj₁ ()))
    is-clean-P-downgrade-nonpos (S z) (inj₂ (inj₂ ()))
    is-clean-P-downgrade-nonpos (P z) (inj₂ (inj₂ p)) = inj₂ p

    abs-S-stack
        : (n : ℕ) 
        → (p : IsClean (S-stack n))
        → abs (S-stack n) p ≡ n
    abs-S-stack ℕ.zero (inj₁ tt) = refl
    abs-S-stack ℕ.zero (inj₂ (inj₁ ()))
    abs-S-stack ℕ.zero (inj₂ (inj₂ ()))
    abs-S-stack (ℕ.suc n) p@(inj₂ (inj₁ isPos)) = 
        ≡begin 
            abs (S-stack (ℕ.suc n)) p
        ≡⟨⟩
            abs (S (S-stack n)) p
        ≡⟨⟩
            ℕ.suc (abs (S-stack n) p')
        ≡⟨ cong ℕ.suc $ abs-S-stack n p' ⟩
            ℕ.suc n
        ≡∎
        where
            p' : IsClean (S-stack n)
            p' = is-clean-S-downgrade {S-stack n} p
    S-stack-abs
        : (z : ℤ')
        → (p : IsClean z )
        → (H : IsZero z ⊎ IsPos z)
        → S-stack (abs z p) ≡ z
    S-stack-abs O     p@(inj₁ isZero)       _ = refl 
    S-stack-abs O     p@(inj₂ (inj₁ ()))
    S-stack-abs O     p@(inj₂ (inj₂ ()))
    S-stack-abs (S z) p@(inj₂ (inj₁ isPos)) _ =  
        ≡begin 
            S-stack (abs (S z) p)
        ≡⟨⟩
            S-stack (ℕ.suc (abs z p'))
        ≡⟨⟩
            S (S-stack (abs z p'))
        ≡⟨ cong S $ S-stack-abs z p' p'' ⟩
            S z 
        ≡∎
        where
            p' : IsClean z
            p' = is-clean-S-downgrade {z} p
            p'' : IsZero z ⊎ IsPos z
            p'' = is-clean-S-downgrade-nonneg z p
    S-stack-abs (P z) p@(inj₂ (inj₂ isNeg)) (inj₁ ())
    S-stack-abs (P z) p@(inj₂ (inj₂ isNeg)) (inj₂ ())

    abs-P-stack
        : (n : ℕ) 
        → (p : IsClean (P-stack n))
        → abs (P-stack n) p ≡ n
    abs-P-stack ℕ.zero (inj₁ tt) = refl
    abs-P-stack ℕ.zero (inj₂ (inj₁ ()))
    abs-P-stack ℕ.zero (inj₂ (inj₂ ()))
    abs-P-stack (ℕ.suc n) p@(inj₂ (inj₂ isNeg)) = 
        ≡begin 
            abs (P-stack (ℕ.suc n)) p
        ≡⟨⟩
            abs (P (P-stack n)) p
        ≡⟨⟩
            ℕ.suc (abs (P-stack n) p')
        ≡⟨ cong ℕ.suc $ abs-P-stack n p' ⟩
            ℕ.suc n
        ≡∎
        where
            p' : IsClean (P-stack n)
            p' = is-clean-P-downgrade {P-stack n} p
    P-stack-abs
        : (z : ℤ')
        → (p : IsClean z )
        → (H : IsZero z ⊎ IsNeg z)
        → P-stack (abs z p) ≡ z
    P-stack-abs O     p@(inj₁ isZero)       _ = refl 
    P-stack-abs O     p@(inj₂ (inj₁ ()))
    P-stack-abs O     p@(inj₂ (inj₂ ()))
    P-stack-abs (P z) p@(inj₂ (inj₂ isNeg)) _ =  
        ≡begin 
            P-stack (abs (P z) p)
        ≡⟨⟩
            P-stack (ℕ.suc (abs z p'))
        ≡⟨⟩
            P (P-stack (abs z p'))
        ≡⟨ cong P $ P-stack-abs z p' p'' ⟩
            P z 
        ≡∎
        where
            p' : IsClean z
            p' = is-clean-P-downgrade {z} p
            p'' : IsZero z ⊎ IsNeg z
            p'' = is-clean-P-downgrade-nonpos z p
    P-stack-abs (S z) p@(inj₂ (inj₂ isNeg)) (inj₁ ())
    P-stack-abs (S z) p@(inj₂ (inj₂ isNeg)) (inj₂ ())

    clean-tuple-eq
        : (z z' : ℤ')
        → (p : IsClean z)
        → z ≡ z'
        → Σ[ p' ∈ IsClean z' ] ((z , p) ≡ (z' , p'))
    clean-tuple-eq z z' p H = (p' , prf)
        where
            p' : IsClean z'
            p' = subst IsClean H p
            prf : (z , p) ≡ (z' , p')
            prf = restIsProofIrrel {A = ℤ'} {B = IsClean} isCleanIrrel {z} {z'} p p' H
