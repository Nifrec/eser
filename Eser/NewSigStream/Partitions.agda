-- Module      : Eser.NewSigStream.Partitions
-- Description : COnversion from bijective partitions to enumerations.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- If a type A can be divided into a ℕ-indexed collection
-- of non-empty finite sets ("chunks"), 
-- such that every term of A occurs exactly once
-- in exactly one such set, then one obtains an equivalence A ≃ ℕ.
--
-- This is similar to how the Haskell-library "Feat" represents enumerations,
-- but here it is dependently typed and proven internally correct.
-- (See Duregård, Jonas, et al. 
--  ‘Feat: Functional Enumeration of Algebraic Types’. 
--  ACM SIGPLAN Notices, vol. 47, no. 12, Sep. 2012, pp. 61–72. 
--  ACM Digital Library, https://doi.org/10.1145/2430532.2364515.)

{-# OPTIONS --safe #-}

open import Level hiding (suc)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Data.Empty
open import Data.Fin using (Fin ; toℕ ; fromℕ<)
open import Data.Fin.Properties
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)
open import Data.Vec as Vec
open import Data.Vec.Properties
open import Function hiding (_↔_)

open import Eser.Logic
open import Eser.Aux using (restIsProofIrrel ; uip ; m<n→Sm<n⊎Sm≡n ; m<m+1+n)
open import Eser.Equivalences.Notation
open import Eser.Equivalences.Properties

module Eser.NewSigStream.Partitions where

Chunking : (A : Set) → Set
Chunking A = ℕ → Σ[ m ∈ ℕ ] Vec A (suc m)

SubIdx : {A : Set} → Chunking A → ℕ → Set
SubIdx f i = Fin (suc $ proj₁ $ f i)

Idx : {A : Set} → Chunking A → Set
Idx f = Σ[ i ∈ ℕ ] (SubIdx f i)

_!!!_ : {A : Set} → (f : Chunking A) → Idx f → A
f !!! (i , j) = Vec.lookup (proj₂ $ f i) j

record Partition (A : Set) : Set where
    field
        chunks : Chunking A
        -- Each element occurs in some chunk.
        complete : (a : A) → Σ[ ij ∈ (Idx chunks) ] a ≡ chunks !!! ij
        -- Chunks are disjoint and have no duplicates,
        -- i.e., elements occur in at most one chunk and therein at most once.
        unique 
            : (ij hk : Idx chunks) 
            → (chunks !!! ij) ≡ (chunks !!! hk) 
            → ij ≡ hk


partitionToEnum : {A : Set} → Partition A → A ≃ ℕ
partitionToEnum {A} p = mk≃' f f⁻¹ invˡ invʳ
    where
        chunks   : Chunking A
        chunks   = Partition.chunks p
        complete = Partition.complete p
        unique   = Partition.unique p

        infix 50 ⨁
        -- ⨁ i is the sum of sizes of chunks with indices smaller than i.
        -- (The symbol is `bigoplus`).
        ⨁ : ℕ → ℕ
        ⨁ 0 = 0
        ⨁ (suc i) = ⨁ i + suc (proj₁ (chunks i))

        -- Taking a few steps within a chunk is always smaller than
        -- taking as many steps as elements within the chunk,
        -- as that would get you to the first element of the next chunk.
        step-in-chunk
            : {i k : ℕ}
            → (j : SubIdx chunks i)
            → i < k
            → ⨁ i + toℕ j < ⨁ k
        step-in-chunk {i} {k@(suc k')} j i<k  = cases (m<n→Sm<n⊎Sm≡n i<k)
            where
                cases 
                    : (p : (suc i < k) ⊎ (suc i ≡ k))
                    → ⨁ i + toℕ j < ⨁ k
                cases (inj₁ 1+i<k) = Data.Nat.Properties.<-trans IH H₀
                    where
                        i<k' : i < k'
                        i<k' = s≤s⁻¹ 1+i<k
                        IH : ⨁ i + toℕ j < ⨁ k'
                        IH = step-in-chunk j i<k'
                        H₀ : ⨁ k' < ⨁ (suc k')
                        H₀ = m<m+1+n (⨁ k') (proj₁ $ chunks k')

                cases (inj₂ 1+i≡k) = 
                    subst (λ x → ⨁ i + toℕ j < ⨁ x) 1+i≡k H₁
                    where
                        n : ℕ
                        n = suc $ proj₁ $ chunks i
                        H₀ : toℕ j < n
                        H₀ = toℕ<n j
                        H₁ : ⨁ i + toℕ j < ⨁ (suc i)
                        H₁ = +-monoʳ-< (⨁ i) H₀ 
        ⨁toℕ-injective
            : (i i' : ℕ)
            → (j : SubIdx chunks i)
            → (j' : SubIdx chunks i')
            → ⨁ i + toℕ j ≡ ⨁ i' + toℕ j'
            → (i , j) ≡ (i' , j')
        ⨁toℕ-injective i i' j j' eq = cases (Data.Nat.<-cmp i i')
            where
                cases : Tri (i < i') (i ≡ i') (i > i') → (i , j) ≡ (i' , j')
                cases (tri< i<i' i≢i' i'≮i) = ⊥-elim $ n≮n n H₁
                    where
                        n : ℕ
                        n = ⨁ i + toℕ j
                        H₀ : ⨁ i + toℕ j < ⨁ i' + toℕ j'
                        H₀ = <-≤-trans (step-in-chunk j i<i') 
                                       (m≤m+n (⨁ i') (toℕ j'))
                        H₁ : n < n
                        H₁ = subst (n <_) (sym eq) H₀
                cases (tri≈ i≮i' refl i'≮i) = cong (i ,_) j≡j'
                    where
                        j≡j' : j ≡ j'
                        j≡j' = toℕ-injective 
                            $ (+-cancelˡ-≡ (⨁ i) (toℕ j) (toℕ j')eq)
                cases (tri> i≮i' i≢i' i'<i) = ⊥-elim $ n≮n n H₁
                    where
                        n : ℕ
                        n = ⨁ i' + toℕ j'
                        H₀ : ⨁ i' + toℕ j' < ⨁ i + toℕ j
                        H₀ = <-≤-trans (step-in-chunk j' i'<i) 
                                       (m≤m+n (⨁ i) (toℕ j))
                        H₁ : n < n
                        H₁ = subst (n <_) eq H₀


        -- Check if a number is the maximum number in a finite set.
        isMax
            : {n : ℕ}
            → (x : Fin (suc n))
            →  (toℕ x < n) ⊎ (toℕ x ≡ n)
        isMax x = m<1+n⇒m<n∨m≡n $ toℕ<n x

        -- Increment a chunk index, jumping to the next chunk if we are at the
        -- end of the current chunk.
        increment 
            : (i : ℕ)
            → (j : SubIdx chunks i)
            → Σ[ i' ∈ ℕ ] 
              Σ[ j' ∈ SubIdx chunks i' ] 
              suc (⨁ i + toℕ j) ≡ ⨁ i' + toℕ j'
        increment i j = cases $ isMax j
            where
                n : ℕ
                n = proj₁ $ chunks i
                cases 
                    : (toℕ j < n) ⊎ (toℕ j ≡ n)
                    → Σ[ i' ∈ ℕ ] 
                      Σ[ j' ∈ SubIdx chunks i' ] 
                      suc (⨁ i + toℕ j) ≡ ⨁ i' + toℕ j'
                cases (inj₁ j<n) = (i , fromℕ< 1+j<1+n , prf)
                    where
                        1+j<1+n : suc (toℕ j) < suc n
                        1+j<1+n = s≤s j<n

                        prf : suc (⨁ i + toℕ j) ≡ ⨁ i + toℕ (fromℕ< 1+j<1+n)
                        prf = sym $ 
                            ≡begin 
                                ⨁ i + toℕ (fromℕ< 1+j<1+n) 
                            ≡⟨ cong (⨁ i +_) $ toℕ-fromℕ< 1+j<1+n ⟩
                                ⨁ i + suc (toℕ j)
                            ≡⟨ +-suc (⨁ i) (toℕ j) ⟩
                                suc (⨁ i + toℕ j)
                            ≡∎
                            
                cases (inj₂ j≡n) = (suc i , Fin.zero , prf)
                    where
                        prf : suc (⨁ i + toℕ j) 
                              ≡ 
                              ⨁ (suc i) + toℕ (Fin.zero {suc n})
                        prf = sym $ 
                            ≡begin 
                                ⨁ (suc i) + toℕ (Fin.zero {suc n}) 
                            ≡⟨⟩
                                ⨁ i + suc n + 0
                            ≡⟨ +-identityʳ (⨁ i + suc n) ⟩
                                ⨁ i + suc n
                            ≡⟨ cong (λ x → ⨁ i + suc x) $ sym j≡n ⟩
                                ⨁ i + suc (toℕ j)
                            ≡⟨ +-suc (⨁ i) (toℕ j) ⟩
                                suc (⨁ i + toℕ j)
                            ≡∎

        -- Data structure for recursively finding the (n+1)th term of A
        -- in the partition; concat all finite chunks
        -- and linearly search.
        -- Second argument (b) is the number of steps still to take.
        -- This is given as a second argument, otherwise the termination
        -- checker would need to use a depth of 2 to see that the function `rec`
        -- below is structurally recursive, since it recurses on b.
        State : ℕ → ℕ → Set
        State n b = 
            Σ[ i ∈ ℕ ]               -- Current chunk.
            Σ[ j ∈ SubIdx chunks i ] -- Current position within current chunk.
            b + ⨁ i + toℕ j ≡ n      -- Correctness proof.         


        rec : (n b : ℕ) 
            → State n b
            → Σ[ i ∈ ℕ ] 
              Σ[ j ∈ SubIdx chunks i ] 
              ⨁ i + toℕ j ≡ n
        rec n 0 (i , j , prf) = (i , j , prf)
        rec n (suc b) (i , j , prf) = rec n b (i' , j' , prf')
            where
                incr : Σ[ i' ∈ ℕ ] 
                       Σ[ j' ∈ SubIdx chunks i' ] 
                       suc (⨁ i + toℕ j) ≡ ⨁ i' + toℕ j'
                incr = increment i j
                i' = proj₁ incr
                j' = proj₁ $ proj₂ incr
                i+j-prf = proj₂ $ proj₂ incr

                prf' = 
                    ≡begin 
                        b + ⨁ i' + toℕ j'
                    ≡⟨ +-assoc b (⨁ i') (toℕ j') ⟩
                        b + (⨁ i' + toℕ j')
                    ≡⟨ cong (b +_) $ sym i+j-prf ⟩
                        b + suc (⨁ i + toℕ j)
                    ≡⟨ +-suc b (⨁ i + toℕ j) ⟩
                        suc b + (⨁ i + toℕ j)
                    ≡⟨ sym $ +-assoc (suc b) (⨁ i) (toℕ j) ⟩
                        suc b + ⨁ i + toℕ j
                    ≡⟨ prf ⟩
                        n
                    ≡∎
                    
        rec-outp-to-idx
            : {n : ℕ}
            → Σ[ i ∈ ℕ ] 
              Σ[ j ∈ SubIdx chunks i ] 
              ⨁ i + toℕ j ≡ n
            → Idx chunks
        rec-outp-to-idx (i , j , _) = (i , j)

        f : A → ℕ
        f a = ⨁ i + toℕ j
            module FImpl where
                i : ℕ
                i = proj₁ $ proj₁ $ complete a
                j : SubIdx chunks i
                j = proj₂ $ proj₁ $ complete a

        f⁻¹ : ℕ → A
        f⁻¹ n = chunks !!! (rec-outp-to-idx $ rec n n (0 , Fin.zero , prf))
            module FInvImpl where
                prf : n + 0 + 0 ≡ n
                prf = 
                    ≡begin 
                        n + 0 + 0
                    ≡⟨ +-identityʳ (n + 0) ⟩
                        n + 0 
                    ≡⟨ +-identityʳ n ⟩
                        n
                    ≡∎
                    
        invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
        invˡ {n} refl = 
            ≡begin 
                f (f⁻¹ n)
            ≡⟨⟩
                f a
            ≡⟨⟩
                ⨁ i + toℕ j
            ≡⟨ cong (λ (i , j) → ⨁ i + toℕ j) ij≡i'j' ⟩
                ⨁ i' + toℕ j'
            ≡⟨ eq ⟩
                n
            ≡∎
            where
                open FInvImpl n using (prf)

                rec-outp = rec n n (0 , Fin.zero , prf)
                i' = proj₁ rec-outp 
                j' = proj₁ $ proj₂ $ rec-outp 
                eq : ⨁ i' + toℕ j' ≡ n
                eq = proj₂ $ proj₂ $ rec-outp

                a : A
                a = chunks !!! (i' , j')

                open FImpl a using (i ; j)

                ij≡i'j' : (i , j) ≡ (i' , j')
                ij≡i'j' = unique (i , j) (i' , j') (sym $ proj₂ $ complete a)


            
        invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
        invʳ {a} refl =
            ≡begin 
                f⁻¹ (f a)
            ≡⟨⟩
                f⁻¹ (⨁ i + toℕ j)
            ≡⟨⟩
                chunks !!! (i' , j')
            ≡⟨ cong (chunks !!!_) i'j'≡ij ⟩
                chunks !!! (i , j)
            ≡⟨ sym $ proj₂ $ complete a ⟩
                a
            ≡∎
            where
                open FImpl a using (i ; j)
                n : ℕ
                n = (⨁ i + toℕ j)

                open FInvImpl n using (prf)

                rec-outp = rec n n (0 , Fin.zero , prf)
                i' = proj₁ rec-outp 
                j' = proj₁ $ proj₂ $ rec-outp 
                eq : ⨁ i' + toℕ j' ≡ (⨁ i + toℕ j)
                eq = proj₂ $ proj₂ $ rec-outp
                i'j'≡ij : (i' , j') ≡ (i , j)
                i'j'≡ij = ⨁toℕ-injective i' i j' j eq


            

