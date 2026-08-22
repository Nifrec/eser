-- Module      : Eser.SigStream.EnumStream
-- Description : Streams that enumerate a type.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- 𝐄𝐧𝐮𝐦𝐒𝐭𝐫𝐞𝐚𝐦(A)
--  Stream that includes every term of A exactly once.
--------------------------------------------------------------------------------

{-# OPTIONS --guardedness #-}

open import Level hiding (suc)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Function hiding (_↔_)
open import Codata.Guarded.Stream
open import Codata.Guarded.Stream.Properties

open import Eser.Aux using (_↔_)
open import Eser.Equivalences.Notation using (_≃_)
open import Eser.Equivalences.Properties using (mk≃')

module Eser.SigStream.EnumStream where

    -- Uniqueness : every element of A occurs at most once in the stream.
    -- We define it as "lookup is injective".
    Unique : {A : Set} → (s : Stream A) → Set
    Unique {A} s = (n m : ℕ) → lookup s n ≡ lookup s m → n ≡ m

    -- Completeness : every element of A occurs at least once in the stream.
    -- We define it as "lookup is surjective".
    Complete : {A : Set} → (s : Stream A) → Set
    Complete {A} s = (a : A) → Σ[ n ∈ ℕ ] lookup s n ≡ a

    isEnumStream : {A : Set} → (s : Stream A) → Set
    isEnumStream s = Unique s × Complete s

    -- There exists an enumeration stream for A iff A is equivalent to ℕ.
    -- (Note : this only proves implications in both directions,
    -- not an equivalence between types. The latter would involve
    -- proving equalities between streams, which seems problematic).
    theorem-enumStream 
        : {A : Set}
        → (Σ[ s ∈ Stream A ] isEnumStream s) ↔ (A ≃ ℕ)
    theorem-enumStream {A} = (left , right)
        where
            left : Σ[ s ∈ Stream A ] isEnumStream s → (A ≃ ℕ)
            left (s , unique , complete) = mk≃' φ φ⁻¹ invˡ invʳ
                where
                    φ : A → ℕ
                    φ = proj₁ ∘ complete

                    φ⁻¹ : ℕ → A
                    φ⁻¹ = lookup s

                    invˡ : Inverseˡ _≡_ _≡_ φ φ⁻¹
                    invˡ {n} refl = unique m n H
                        where
                            m : ℕ
                            m = φ (φ⁻¹ n) 
                            -- That is: m ≗ proj₁ (complete $ lookup s n)

                            H : lookup s m ≡ lookup s n
                            H = proj₂ (complete $ lookup s n)

                    invʳ : Inverseʳ _≡_ _≡_ φ φ⁻¹
                    invʳ {a} {x} refl = 
                        begin 
                            φ⁻¹ (φ a)
                        ≡⟨⟩
                            lookup s (proj₁ $ complete a)
                        ≡⟨ proj₂ $ complete a ⟩
                            a
                        ∎


            right : (A ≃ ℕ) → Σ[ s ∈ Stream A ] isEnumStream s
            right A≃ℕ = (s , unique , complete)
                where
                    open Eser.Equivalences.Notation.EquivShorthands A≃ℕ
                    s : Stream A
                    s = tabulate φ⁻¹ 

                    unique : Unique s
                    unique n m eq =
                            begin 
                                n
                            ≡⟨ sym $ φ∘φ⁻¹≈id n ⟩
                                φ (φ⁻¹ n)
                            ≡⟨ sym $ cong φ (lookup-tabulate n φ⁻¹) ⟩
                                φ (lookup s n)
                            ≡⟨ cong φ eq ⟩
                                φ (lookup s m)
                            ≡⟨ cong φ (lookup-tabulate m φ⁻¹) ⟩
                                φ (φ⁻¹ m)
                            ≡⟨ φ∘φ⁻¹≈id m ⟩
                                m
                            ∎

                    complete : Complete s
                    complete a = (φ a , eq)
                        where
                            eq : lookup s (φ a) ≡ a
                            eq = 
                                begin 
                                    lookup s (φ a)
                                ≡⟨⟩
                                    lookup (tabulate φ⁻¹) (φ a)
                                ≡⟨ lookup-tabulate (φ a) φ⁻¹ ⟩
                                    (φ⁻¹ ∘ φ) a
                                ≡⟨ φ⁻¹∘φ≈id a ⟩
                                    a
                                ∎
                        

