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
