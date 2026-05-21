-- Module      : Eser.Quotients
-- Description : Defining a quotient type of an enumerable type.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- Constructing quotient types
--
-- Given an enumerable type A with φ : A ≃ ℕ
-- and an equivalence relation represented by a normal-form function
-- f : NFFun,
-- we can define the quotient type φ / f 
-- whose terms are representatives of equivalence classes of funToRel f.
-- Those representatives, AKA normal forms, are the least elements
-- of equivalence classes in the enumertion of A according to φ.
-- Normal forms are exactly the fixpoints of f,
-- since f n ≤ n and f (f n) ≡ f n.
--
-- #TODO: also add support for A ≃ Fin n. Low priority because quotients can
-- obviously be constructed for such types.
--------------------------------------------------------------------------------

open import Level
open import Data.Bool hiding (_≤_ ; _<_ ; _≤?_)
open import Data.Bool.Properties using (¬-not ; not-¬)
open import Data.Nat hiding (_/_)
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Data.Product
open import Relation.Binary.Structures
open import Data.Fin hiding (_≤_ ; _≤?_)
open import Data.Nat.Properties using (≤-refl ; ≤-trans ; ≤-<-trans ; n≤0⇒n≡0 
                                       ; n≤1+n ; m≤n⇒m<n∨m≡n ; _≤?_ ; ≰⇒≥)
open import Data.Fin.Properties using (toℕ<n)
open import Relation.Nullary hiding (stable)
open import Function hiding (_↔_)

open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)

open import Eser.Aux
open import Eser.Equivalences
open import Eser.EqRel

module Eser.Quotients where

-- Quotient type of an enumerated type A by a relation (the latter being
-- represented by a normal-form function).
-- It is represented as the set of normal forms,
-- i.e., fixpoints of the normal-form function.
-- I.e., a ∈ A is the representative of an equivalence class
-- iff its ℕ-encoding φ(a) is a normal form
-- iff φ(a) is a fixpoint of the normal-form function.
_/_ : {A : Set} → (A ≃ ℕ) → NFFun → Set
_/_ {A} A≃ℕ (nf , nfleq , nffix) = Σ[ a ∈ A ](IsFixpoint nf (φ a))
    where
        φ : A → ℕ
        φ = ≃-to A≃ℕ

--------------------------------------------------------------------------------
-- Morphisms in and out of quotients.
--
-- The notation is based on §4 of 
--      Nuo Li, "Quotient Types in Type Theory" (2014)
-- The proofs are quite trivial, since our quotient elements are defined
-- in terms of a normal-from function.
--------------------------------------------------------------------------------

module Morphisms (A : Set) (A' : A ≃ ℕ) (R : NFFun) where

    φ : A → ℕ
    φ = ≃-to A'

    φ⁻¹ : ℕ → A
    φ⁻¹ = ≃-from A'

    φ∘φ⁻¹≈id : (φ ∘ φ⁻¹) ≈ id
    φ∘φ⁻¹≈id = ≃-toFrom A'

    φ⁻¹∘φ≈id : (φ⁻¹ ∘ φ) ≈ id
    φ⁻¹∘φ≈id = ≃-fromTo A'

    φ⁻¹-injective : Injective _≡_ _≡_ φ⁻¹
    φ⁻¹-injective = ≃-from-injective A'

    nf : ℕ → ℕ
    nf = proj₁ R

    nffix : (n : ℕ) → nf (nf n) ≡ nf n
    nffix = proj₃ R

    -- The relation encoded in R.
    -- Two elements are related if their normal forms (in ℕ) are equal.
    _∼_ : Rel A _
    a ∼ a' = (nf $ φ a) ≡ (nf $ φ a')


    IsNormal : A → Set
    IsNormal a = IsFixpoint nf (φ a)

    isNormalIrrel : (a : A) → Relation.Nullary.Irrelevant (IsNormal a)
    isNormalIrrel a = Data.Nat.Properties.≡-irrelevant

    -- Quotient map
    [_] : A → A' / R
    [_] a = (φ⁻¹ (nf (φ a)) , isNF)
        where
            [a] : A
            [a] = φ⁻¹ (nf (φ a))

            isNF : nf (φ [a]) ≡ φ [a]
            isNF = ≡begin 
                    (nf $ φ [a])
                ≡⟨⟩
                    (nf $ φ $ φ⁻¹ $ nf $ φ a)
                ≡⟨ cong nf (φ∘φ⁻¹≈id (nf $ φ a)) ⟩
                    (nf $ nf $ φ a)
                ≡⟨ nffix (φ a) ⟩
                    (nf $ φ a)
                ≡⟨⟩
                    (id $ nf $ φ a)
                ≡⟨ sym $ φ∘φ⁻¹≈id (nf (φ a)) ⟩ 
                    (φ $ φ⁻¹ $ nf $ φ a)
                ≡⟨⟩
                    φ (φ⁻¹ $ nf $ φ a)  
                ≡⟨⟩
                    φ [a]
                ≡∎

    sound : (a a' : A) → a ∼ a' → [ a ] ≡ [ a' ]
    sound a a' a∼a' = restIsProofIrrel {A} {B} isNormalIrrel b b' H
        where
            H : (proj₁ [ a ]) ≡ (proj₁ [ a' ])
            H = cong φ⁻¹ a∼a'
            B : A → Set
            B = IsNormal
            b = proj₂ [ a ]
            b' = proj₂ [ a' ]

    -- Embed the quotient back into A, by picking out the element corresponding
    -- to the normal form of the class.
    emb : A' / R → A
    emb = proj₁

    complete : (a : A) → (emb ∘ [_]) (a) ∼ a
    complete a = 
        -- To show: nf $ φ $ emb $ [ a ] ≡ nf $ φ a
        ≡begin 
            (nf $ φ $ emb [ a ])
        ≡⟨⟩
            (nf $ φ $ φ⁻¹ $ nf $ φ a) 
        ≡⟨ cong nf (φ∘φ⁻¹≈id (nf $ φ a)) ⟩
            (nf $ nf $ φ a)
        ≡⟨ nffix (φ a) ⟩
            (nf $ φ a)
        ≡∎

    stable : ([_] ∘ emb) ≈ id {_} {A' / R}
    stable (a , p) = restIsProofIrrel {A} {B} B-irrel p' p a'≡a
        where
            B : A → Set
            B a = nf (φ a) ≡ φ a
            B-irrel : (a : A) → Relation.Nullary.Irrelevant (B a)
            B-irrel a = Data.Nat.Properties.≡-irrelevant

            a' = proj₁ [ (emb (a , p)) ]
            p' = proj₂ [ (emb (a , p)) ]
            a'≡a : a' ≡ a
            a'≡a =
                ≡begin 
                    a'
                ≡⟨⟩
                    proj₁ [ (emb (a , p)) ]
                ≡⟨⟩
                    proj₁ [ a ]
                ≡⟨⟩
                    (φ⁻¹ $ nf $ φ a)
                ≡⟨ cong φ⁻¹ p ⟩
                    (φ⁻¹ $ φ a)
                ≡⟨ φ⁻¹∘φ≈id a ⟩
                    a
                ≡∎

    effective : {a b : A} → [ a ] ≡ [ b ] → a ∼ b
    effective {a} {b} H = φ⁻¹-injective (cong proj₁ H)

    quotLift 
        : {B : Set}
        → (g : A → B) 
        → ({a a' : A} → (a ∼ a') → (g a ≡ g a')) 
        → A' / R → B
    quotLift g H = g ∘ emb

    qind
        : {B : (A' / R) → Set}
        → ((a : A) → B [ a ])
        → (q : (A' / R))
        → B q
    qind {B} g q@(a , isNormal) = subst B [a]≡q outp
        where
            -- This is the right output, but we need to substitute the index
            -- [ a ] by q.
            outp : B [ a ]
            outp = g a
            H : proj₁ [ a ] ≡ a
            H = ≡begin 
                    (φ⁻¹ ∘ nf ∘ φ) a
                ≡⟨  cong φ⁻¹ isNormal ⟩
                    (φ⁻¹ ∘ φ) a
                ≡⟨ φ⁻¹∘φ≈id a ⟩
                    a
                ≡∎
            [a]≡q : [ a ] ≡ q
            [a]≡q = restIsProofIrrel {A} {IsNormal} 
                isNormalIrrel {proj₁ [ a ]} {a} (proj₂ [ a ]) isNormal H

                
    
    deceq : DecidableEquality (A' / R)
    deceq (a , p) (a' , q) = caseDistinction $ deceqA a a'
        where
            deceqA : DecidableEquality A
            deceqA = enumDecEquality {A} A' 
            caseDistinction : Dec (a ≡ a') → Dec ((a , p) ≡ (a' , q))
            caseDistinction (yes H) = yes $ restIsProofIrrel {A} {IsNormal} 
                                                            isNormalIrrel p q H
            caseDistinction (no H) = no $ λ ap≡a'q → H (cong proj₁ ap≡a'q)

    -- The quotient A'/R has proof-irrelevant equalities, AKA is an hSet.
    -- This follows from dedicable equality using Hedberg's theorem
    -- (the latter is in the stdlib).
    ≡-irrel : Relation.Binary.Definitions.Irrelevant {A = A' / R} _≡_ 
    ≡-irrel = ≡-irrelevant
        where
            import Axiom.UniquenessOfIdentityProofs
            open Axiom.UniquenessOfIdentityProofs.Decidable⇒UIP deceq
                using (≡-irrelevant)
