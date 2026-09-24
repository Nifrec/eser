-- Module      : Eser.Signature.NatCoding
-- Description : Encoding and decoding to ℕ of various simple types.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.DivMod
open DivMod
open import Data.Sum
open import Data.Sum.Properties using (inj₂-injective)
open import Data.Product
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)
open import Data.Vec
open import Data.Vec.Relation.Unary.All as All hiding (_∷_)
open import Data.Fin using (Fin ; toℕ ; fromℕ<)
open import Data.Fin.Properties using (toℕ-fromℕ< ; toℕ<n ; toℕ≤n ; fromℕ<-toℕ)
open import Function hiding (_↔_)
open import Function.Consequences.Propositional 
    using (inverseˡ⇒strictlyInverseˡ 
          ; inverseʳ⇒strictlyInverseʳ
          )
open import Relation.Binary.PropositionalEquality

open import Eser.Aux using 
    ( uip 
    ; _≈_ 
    ; restIsProofIrrel 
    ; double-eq-single-eq
    ; double-eq-never-odd
    ; <?-≮ 
    ; <?-<
    ; m∸n<m
    ; doubleSubst
    )
open import Eser.Card
open import Eser.Signature.Definitions
open import Eser.Equivalences.Notation
open import Eser.Equivalences.Properties
open import Eser.NewSigStream.EnumVectors
open import Eser.Partitions
open import Eser.Partitions.Properties
open import Eser.Sum using (sum-disjoined)
open import Eser.DivMod using (a<n→y≡[y*n+a]/n)

module Eser.NatCoding where


module _ {n : ℕ} where
    equiv : Vec ℕ (suc n) ≃ ℕ
    equiv = vec-enum n

    code-vec : Vec ℕ (suc n) → ℕ
    code-vec = Inverse.to equiv

    -- Note: decode-vec' uses a different decoding for each length.
    -- So one must *explicitly* give the target length as well.
    decode-vec' : ℕ → Vec ℕ (suc n)
    decode-vec' = Inverse.from equiv

    decode-code-vec : decode-vec' ∘ code-vec ≈ id
    decode-code-vec = inverseʳ⇒strictlyInverseʳ $ Inverse.inverseʳ equiv

    code-decode-vec' : code-vec ∘ decode-vec' ≈ id
    code-decode-vec' = inverseˡ⇒strictlyInverseˡ $ Inverse.inverseˡ equiv

    code-vec-weight
        : (v : Vec ℕ (suc n))
        → weight v ≤ code-vec v
    code-vec-weight v = subst (λ v → w ≤ code-vec v) (sym eq) 
                              $ enc-larger-than-chunkidx (vec-part n) w j
        where
            w : ℕ
            w = weight v
            j : SubIdx (Partition.chunks (vec-part n)) w
            j = proj₂ $ proj₁ $ Partition.complete (vec-part n) v
            chunks : Chunking (Vec ℕ (suc n))
            chunks = Partition.chunks $ vec-part n
            eq : v ≡ chunks !!! (w , j)
            eq = proj₂ $ Partition.complete (vec-part n) v


    -- The ℕ-encoding of a vector is at least as great as the maximum of its
    -- elements.
    code-vec-lemma
        : (v : Vec ℕ (suc n))
        → All (_≤ (code-vec v)) v
    code-vec-lemma v = All.map f $ elem-weight v
        where
            f : {x : ℕ} → x ≤ weight v → x ≤ code-vec v
            f {x} x≤w = ≤-trans x≤w $ code-vec-weight v
                

-- Variants of above with implicit argument (vector length) made explicit.
decode-vec : (n : ℕ) → ℕ → Vec ℕ (suc n)
decode-vec n = decode-vec' {n}
code-decode-vec : (n : ℕ) → code-vec ∘ (decode-vec n) ≈ id
code-decode-vec n = code-decode-vec' {n}

decode-vec-lemma
    : (n i : ℕ)
    → (v : Vec ℕ (suc n))
    → (v ≡ decode-vec n i)
    → All (_≤ i) v
decode-vec-lemma n i v eq 
    = subst (λ x → All (_≤ x) v) cvv≡i (code-vec-lemma {n} v)
    where
        cvv≡i : code-vec v ≡ i
        cvv≡i = 
            ≡begin 
                code-vec v
            ≡⟨ cong code-vec eq  ⟩
                code-vec (decode-vec n i)
            ≡⟨ code-decode-vec n i ⟩
                i
            ≡∎

Parity : ℕ → Set
Parity n = (Σ[ m ∈ ℕ ] n ≡ m + m) ⊎ (Σ[ m ∈ ℕ ] n ≡ 1 + m + m)

parity' : (n : ℕ) → Parity n
parity' ℕ.zero = inj₁ (0 , refl)
parity' (suc ℕ.zero) = inj₂ (0 , refl) 
parity' (2+ n) = cases (parity' n)
    where
        cases : Parity n → Parity (2+ n)
        cases (inj₁ (m , eq)) = inj₁ (suc m , eq')
            where
                eq' : 2+ n ≡ suc m + suc m
                eq' = 
                    ≡begin 
                        2+ n
                    ≡⟨ cong 2+ eq ⟩
                        2+ (m + m)
                    ≡⟨ cong suc (sym $ +-suc m m) ⟩
                        suc m + suc m
                    ≡∎
        cases (inj₂ (m , eq)) = inj₂ (suc m , eq')
            where
                eq' : 2+ n ≡ 1 + suc m + suc m
                eq' = 
                    ≡begin 
                        2+ n
                    ≡⟨ cong 2+ eq ⟩
                        2+ (1 + m + m)
                    ≡⟨ cong 2+ (sym $ +-suc m m) ⟩
                        2+ m + suc m
                    ≡⟨⟩
                        1 + suc m + suc m
                    ≡∎

is-even-irrel
    : (n m : ℕ)
    → Relation.Nullary.Irrelevant (n ≡ m + m)
is-even-irrel _ _ p q = uip p q

parity-even
    : (m : ℕ)
    → (eq : m + m ≡ m + m)
    → parity' (m + m) ≡ inj₁ (m , eq)
parity-even m eq = cases (parity' (m + m)) refl
    where
        cases 
            : (p : Parity (m + m))
            → parity' (m + m) ≡ p
            → parity' (m + m) ≡ inj₁ (m , eq)
        cases (inj₁ (z , m+m≡z+z)) eq-p =
            ≡begin 
                parity' (m + m)
            ≡⟨ eq-p ⟩
                inj₁ (z , m+m≡z+z)
            ≡⟨ cong inj₁
                $ restIsProofIrrel 
                    {A = ℕ}
                    {B = λ n → m + m ≡ n + n}
                    (is-even-irrel (m + m)) 
                    {z} {m}
                    m+m≡z+z eq z≡m
            ⟩
                inj₁ (m , eq)
            ≡∎
            where
                z≡m : z ≡ m
                z≡m = double-eq-single-eq (sym m+m≡z+z)
        cases (inj₂ (z , m+m≡1+z+z)) = 
            ⊥-elim $ double-eq-never-odd {m} {z} m+m≡1+z+z
is-odd-irrel
    : (n m : ℕ)
    → Relation.Nullary.Irrelevant (n ≡ 1 + m + m)
is-odd-irrel _ _ p q = uip p q

parity-odd
    : (m : ℕ)
    → (eq : 1 + m + m ≡ 1 + m + m)
    → parity' (1 + m + m) ≡ inj₂ (m , eq)
parity-odd m eq = cases (parity' (1 + m + m)) refl
    where
        cases 
            : (p : Parity (1 + m + m))
            → parity' (1 + m + m) ≡ p
            → parity' (1 + m + m) ≡ inj₂ (m , eq)
        cases (inj₁ (z , 1+m+m≡z+z)) eq-p =
            ⊥-elim $ double-eq-never-odd {z} {m} (sym 1+m+m≡z+z)
        cases (inj₂ (z , 1+m+m≡1+z+z)) eq-p = 
            ≡begin 
                parity' (1 + m + m)
            ≡⟨ eq-p ⟩
                inj₂ (z , 1+m+m≡1+z+z)
            ≡⟨ cong inj₂
                $ restIsProofIrrel 
                    {A = ℕ}
                    {B = λ n → 1 + m + m ≡ 1 + n + n}
                    (is-odd-irrel (1 + m + m)) 
                    {z} {m}
                    1+m+m≡1+z+z eq z≡m
            ⟩
                inj₂ (m , eq)
            ≡∎
            where
                z≡m : z ≡ m
                z≡m = double-eq-single-eq (sym $ suc-injective 1+m+m≡1+z+z)


-- Encode the left ℕ as the even numbers,
-- and the right ℕ as the odd numbers.
code-sum-inf : ℕ ⊎ ℕ → ℕ
code-sum-inf (inj₁ n) = n + n
code-sum-inf (inj₂ n) = 1 + n + n

decode-sum-inf : ℕ → ℕ ⊎ ℕ
decode-sum-inf n = cases $ parity' n
    module DecSumInfImpl where
        cases : Parity n → ℕ ⊎ ℕ
        cases (inj₁ (m , _)) = inj₁ m
        cases (inj₂ (m , _)) = inj₂ m

equiv-sum-inf : (ℕ ⊎ ℕ) ≃ ℕ
equiv-sum-inf = mk≃' f f⁻¹ invˡ invʳ
    where
    f : ℕ ⊎ ℕ → ℕ
    f = code-sum-inf
    f⁻¹ : ℕ → ℕ ⊎ ℕ
    f⁻¹ = decode-sum-inf
    invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
    invˡ {n} refl = cases (parity' n) refl
        where
            open DecSumInfImpl n renaming (cases to dec-cases)

            cases : (p : Parity n) → (parity' n ≡ p) → f (f⁻¹ n) ≡ n
            cases (inj₁ (m , n≡m+m)) eq = 
                ≡begin 
                    f (f⁻¹ n)
                ≡⟨⟩
                    f (dec-cases (parity' n))
                ≡⟨ cong (f ∘ dec-cases) eq ⟩
                    f (dec-cases (inj₁ (m , n≡m+m)))
                ≡⟨⟩
                    f (inj₁ m)
                ≡⟨⟩
                    m + m
                ≡⟨ sym n≡m+m ⟩
                    n
                ≡∎
                
            cases (inj₂ (m , n≡1+m+m)) eq =
                ≡begin 
                    f (f⁻¹ n)
                ≡⟨⟩
                    f (dec-cases (parity' n))
                ≡⟨ cong (f ∘ dec-cases) eq ⟩
                    f (dec-cases (inj₂ (m , n≡1+m+m)))
                ≡⟨⟩
                    f (inj₂ m)
                ≡⟨⟩
                    1 + m + m
                ≡⟨ sym n≡1+m+m ⟩
                    n
                ≡∎

    invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
    invʳ {inj₁ m} refl = 
        ≡begin 
            f⁻¹ (f (inj₁ m))
        ≡⟨⟩
            f⁻¹ (m + m)
        ≡⟨⟩
            dec-cases (parity' (m + m))
        ≡⟨ cong dec-cases (parity-even m refl) ⟩
            dec-cases (inj₁ (m , refl))
        ≡⟨⟩
            inj₁ m
        ≡∎
        where
            open DecSumInfImpl (m + m) renaming (cases to dec-cases)
        
    invʳ {inj₂ m} refl =
        ≡begin 
            f⁻¹ (f (inj₂ m))
        ≡⟨⟩
            f⁻¹ (1 + m + m)
        ≡⟨⟩
            dec-cases (parity' (1 + m + m))
        ≡⟨ cong dec-cases (parity-odd m refl) ⟩
            dec-cases (inj₂ (m , refl))
        ≡⟨⟩
            inj₂ m
        ≡∎
        where
            open DecSumInfImpl (1 + m + m) renaming (cases to dec-cases)

code-sum-fin
    : {n : ℕ}
    → Fin n ⊎ ℕ 
    → ℕ
code-sum-fin (inj₁ x) = toℕ x
code-sum-fin {n} (inj₂ x) = x + n

decode-sum-fin
    : {n : ℕ}
    → ℕ
    → Fin n ⊎ ℕ
decode-sum-fin {n} x = cases (x <? n)
    module DecSumFinImpl where
        cases : Dec (x < n) → Fin n ⊎ ℕ
        cases (yes x<n) = inj₁ $ fromℕ< x<n
        cases (no x≮n) =  inj₂ (x ∸ n) 

code-decode-sum-fin
    : {n : ℕ}
    → (code-sum-fin {n} ∘ decode-sum-fin {n} ) ≈ id {A = ℕ}
code-decode-sum-fin {n} x = cases (x <? n) refl
    where
        open DecSumFinImpl {n} x renaming (cases to dec-cases)
        f = code-sum-fin {n}
        f⁻¹ = decode-sum-fin {n}
        cases 
            : (d : Dec (x < n)) 
            → ((x <? n) ≡ d)
            → (f (f⁻¹ x)) ≡ x
        cases (yes x<n) eq = 
            ≡begin 
                f (f⁻¹ x)
            ≡⟨⟩
                f (dec-cases (x <? n))
            ≡⟨ cong (f ∘ dec-cases) eq ⟩
                f (dec-cases (yes x<n))
            ≡⟨⟩
                f (inj₁ $ fromℕ< x<n)
            ≡⟨⟩
                toℕ (fromℕ< x<n)
            ≡⟨ toℕ-fromℕ< x<n ⟩
                x
            ≡∎
        cases (no x≮n) eq = 
            ≡begin 
                f (f⁻¹ x)
            ≡⟨⟩
                f (dec-cases (x <? n))
            ≡⟨ cong (f ∘ dec-cases) eq ⟩
                f (dec-cases (no x≮n))
            ≡⟨⟩
                f (inj₂ $ x ∸ n)
            ≡⟨⟩
                (x ∸ n) + n
            ≡⟨ m∸n+n≡m $ ≮⇒≥ x≮n ⟩
                x
            ≡∎

decode-code-sum-fin
    : {n : ℕ}
    → (decode-sum-fin {n} ∘ code-sum-fin {n} ) ≈ id {A = Fin n ⊎ ℕ}
decode-code-sum-fin {n} (inj₁ x) = 
    ≡begin 
        f⁻¹ (f (inj₁ x))
    ≡⟨⟩
        f⁻¹ (toℕ x)
    ≡⟨⟩
        dec-cases (toℕ x <? n)
    ≡⟨ cong dec-cases $ <?-< x<n ⟩
        dec-cases (yes x<n)
    ≡⟨⟩
        inj₁ (fromℕ< x<n)
    ≡⟨ cong inj₁ $ fromℕ<-toℕ x x<n ⟩
        inj₁ x
    ≡∎
    where
        f = code-sum-fin {n}
        f⁻¹ = decode-sum-fin {n}
        open DecSumFinImpl {n} (toℕ x) renaming (cases to dec-cases)
        x<n : toℕ x < n
        x<n = toℕ<n x
decode-code-sum-fin {n} (inj₂ x) = 
    ≡begin 
        f⁻¹ (f (inj₂ x))
    ≡⟨⟩
        f⁻¹ (x + n)
    ≡⟨⟩
        dec-cases (x + n <? n)
    ≡⟨ cong dec-cases $ <?-≮ x+n≮n ⟩
        dec-cases (no x+n≮n)
    ≡⟨⟩
        inj₂ (x + n ∸ n)
    ≡⟨ cong inj₂ $ m+n∸n≡m x n ⟩
        inj₂ x
    ≡∎
    where
        f = code-sum-fin {n}
        f⁻¹ = decode-sum-fin {n}
        open DecSumFinImpl {n} (x + n) renaming (cases to dec-cases)
        x+n≮n : x + n ≮ n
        x+n≮n = m+n≮n x n

code-sum' : {μ : ℕ∞} → ^ (suc∞ μ) ⊎ ℕ → ℕ
code-sum' {fin n} = code-sum-fin {suc n}
code-sum' {∞} = code-sum-inf

decode-sum' : {μ : ℕ∞} → ℕ → ^ (suc∞ μ) ⊎ ℕ
decode-sum' {fin n} = decode-sum-fin {suc n}
decode-sum' {∞} = decode-sum-inf

code-decode-sum'
    : {μ : ℕ∞}
    → (code-sum' {μ} ∘ decode-sum' {μ} ) ≈ id
code-decode-sum' {fin n} = code-decode-sum-fin {suc n}
code-decode-sum' {∞} = inverseˡ⇒strictlyInverseˡ $ Inverse.inverseˡ equiv-sum-inf

decode-code-sum'
    : {μ : ℕ∞}
    → (decode-sum' {μ} ∘ code-sum' {μ} ) ≈ id
decode-code-sum' {fin n} = decode-code-sum-fin {suc n}
decode-code-sum' {∞} = inverseʳ⇒strictlyInverseʳ $ Inverse.inverseʳ equiv-sum-inf


decode-sum-lemma'
    : {μ : ℕ∞}
    → (x w : ℕ)
    → decode-sum' {μ} x ≡ inj₂ w
    → w < x
decode-sum-lemma' {fin n} (suc x) w eq = cases (suc x <? suc n) refl
    where
        open DecSumFinImpl {suc n} (suc x) renaming (cases to dec-cases)
        cases 
            : (d : Dec (suc x < suc n)) 
            → ((suc x <? suc n) ≡ d)
            → (w < suc x)
        cases (yes 1+x<1+n) eq-d = 
            ⊥-elim $
            sum-disjoined $ 
            ≡begin 
                inj₁ (fromℕ< 1+x<1+n)
            ≡⟨⟩
                dec-cases (yes 1+x<1+n)
            ≡⟨ cong dec-cases (sym eq-d) ⟩
                dec-cases (suc x <? suc n)
            ≡⟨⟩
                decode-sum-fin (suc x)
            ≡⟨ eq ⟩
                inj₂ w
            ≡∎

        cases (no 1+x≮1+n) eq-d = subst (_< (suc x)) 1+x∸1+n≡w 1+x∸1+n<1+x
            where
                1+x∸1+n<1+x : suc x ∸ suc n < suc x
                1+x∸1+n<1+x = m∸n<m x n
                1+x∸1+n≡w : suc x ∸ suc n ≡ w
                1+x∸1+n≡w = inj₂-injective $
                    ≡begin 
                        inj₂ (suc x ∸ suc n)
                    ≡⟨⟩
                        dec-cases (no 1+x≮1+n)
                    ≡⟨ cong dec-cases (sym eq-d) ⟩
                        dec-cases (suc x <? suc n)
                    ≡⟨⟩
                        decode-sum-fin (suc x)
                    ≡⟨ eq ⟩
                        inj₂ w
                    ≡∎

decode-sum-lemma' {∞} x w eq = cases (parity' x) refl
        where
            open DecSumInfImpl x renaming (cases to dec-cases)
            cases 
                : (p : Parity x) 
                → (parity' x ≡ p) 
                → w < x
            cases (inj₁ (m , x≡m+m)) eq-p = 
                ⊥-elim $
                sum-disjoined $ 
                ≡begin 
                    inj₁ m
                ≡⟨⟩
                    dec-cases (inj₁ (m , x≡m+m))
                ≡⟨ cong dec-cases (sym eq-p) ⟩
                    dec-cases (parity' x)
                ≡⟨⟩
                    decode-sum-inf x
                ≡⟨ eq ⟩
                    inj₂ w
                ≡∎

            cases (inj₂ (m , x≡1+m+m)) eq-p = 
                doubleSubst _<_ m≡w (sym x≡1+m+m) m<1+m+m
                where
                    m<1+m+m : m < 1 + m + m
                    m<1+m+m  = <-≤-trans (n<1+n m) (m≤m+n (suc m) m)

                    m≡w : m ≡ w
                    m≡w = 
                        inj₂-injective $ 
                        ≡begin 
                            inj₂ m
                        ≡⟨⟩
                            dec-cases (inj₂ (m , x≡1+m+m))
                        ≡⟨ cong dec-cases (sym eq-p) ⟩
                            dec-cases (parity' x)
                        ≡⟨⟩
                            decode-sum-inf x
                        ≡⟨ eq ⟩
                            inj₂ w
                        ≡∎

code-pair-fin 
    : {n : ℕ}
    → Fin (suc n) × ℕ
    → ℕ
code-pair-fin {n'} (x , y) = toℕ x + y * (suc n')

decode-pair-fin
    : {n : ℕ}
    → ℕ
    → Fin (suc n) × ℕ
decode-pair-fin {n'} z = (remainder d , quotient d)
    where
        n : ℕ
        n = suc n'
        d : DivMod z n
        d = z divMod n

code-decode-pair-fin
    : {n : ℕ}
    → (code-pair-fin {n} ∘ decode-pair-fin {n}) ≈ id {A = ℕ}
code-decode-pair-fin {n} z = sym $ property (z divMod suc n)

decode-code-pair-fin
    : {n : ℕ}
    → (decode-pair-fin {n} ∘ code-pair-fin {n}) ≈ id {A = Fin (suc n) × ℕ}
decode-code-pair-fin {n'} (x , y) = 
    ≡begin 
        dec (enc (x , y))
    ≡⟨⟩
        dec (toℕ x + y * n)
    ≡⟨⟩
        (remainder d , quotient d)
    ≡⟨ cong₂ _,_ rd≡x qd≡y ⟩
        (x , y)
    ≡∎
    where
        dec = decode-pair-fin {n'}
        enc = code-pair-fin {n'}
        n : ℕ
        n = suc n'
        z : ℕ
        z = toℕ x + y * n

        d : DivMod (toℕ x + y * n) n
        d = z divMod n

        x<n : toℕ x < n
        x<n = toℕ<n x

        eq : z % n ≡ toℕ x
        eq = 
            ≡begin 
                (toℕ x + y * n) % n   
            ≡⟨ [m+kn]%n≡m%n (toℕ x) y n ⟩
                toℕ x % n
            ≡⟨ m≤n⇒m%n≡m (s≤s⁻¹ x<n) ⟩
                toℕ x
            ≡∎
            
        f :  Σ[ a ∈ ℕ ] a < n → Fin n
        f (a , a<n) = fromℕ< {a} a<n
        
        rd≡x : remainder d ≡ x
        rd≡x =
            ≡begin 
                remainder d
            ≡⟨⟩
                (toℕ x + y * n) mod n
            ≡⟨⟩
                fromℕ< (m%n<n z n)
            ≡⟨⟩
                f (z % n , m%n<n z n)
            ≡⟨ cong f
                $ restIsProofIrrel (λ a → <-irrelevant {x = a} {y = n}) 
                    (m%n<n z n) x<n eq 
            ⟩
                f (toℕ x , x<n)
            ≡⟨⟩
                fromℕ< x<n
            ≡⟨ fromℕ<-toℕ x x<n ⟩
                x
            ≡∎

        qd≡y : quotient d ≡ y
        qd≡y = 
            ≡begin 
                quotient d
            ≡⟨⟩
                z / n
            ≡⟨⟩
                (toℕ x + y * n) / n
            ≡⟨ cong (_/ n) $ +-comm (toℕ x) (y * n) ⟩
                (y * n + toℕ x) / n
            ≡⟨ sym $ a<n→y≡[y*n+a]/n y x<n ⟩
                y
            ≡∎
            
decode-pair-lemma-fin
    : {n : ℕ}
    → (i y : ℕ)
    → (x : Fin (suc n))
    → decode-pair-fin i ≡ (x , y)
    → y ≤ i
decode-pair-lemma-fin {n'} i y x eq = y≤i
    where
        n : ℕ
        n = suc n'
        
        d : DivMod i n
        d = i divMod n

        qd≤i : quotient d ≤ i
        qd≤i = m/n≤m i n

        y≤i : y ≤ i
        y≤i = subst (_≤ i) (cong proj₂ eq) qd≤i
            
toVec : ℕ × ℕ → Vec ℕ 2
toVec (x , y) = x ∷ y ∷ []
toPair : Vec ℕ 2 → ℕ × ℕ
toPair (x ∷ y ∷ []) = (x , y)

toVec-toPair : (toVec ∘ toPair) ≈ id {A = Vec ℕ 2}
toVec-toPair (x ∷ y ∷ []) = refl
toPair-toVec : (toPair ∘ toVec) ≈ id {A = ℕ × ℕ}
toPair-toVec (x , y) = refl

pairs≃vecs : ℕ × ℕ ≃ Vec ℕ 2
pairs≃vecs = mk≃' f f⁻¹ invˡ invʳ
    where
    f : ℕ × ℕ  → Vec ℕ 2
    f = toVec
    f⁻¹ : Vec ℕ 2 → ℕ × ℕ 
    f⁻¹ = toPair
    invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
    invˡ {x ∷ y ∷ []} refl = refl
    invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
    invʳ {(x , y)} refl = refl

code-pair-inf : ℕ × ℕ → ℕ
code-pair-inf = code-vec ∘ toVec 
decode-pair-inf : ℕ → ℕ × ℕ
decode-pair-inf = toPair ∘ (decode-vec 1)

decode-code-pair-inf : (decode-pair-inf ∘ code-pair-inf) ≈ id {A = ℕ × ℕ}
decode-code-pair-inf p =
    ≡begin 
        dec (enc p) 
    ≡⟨⟩
        (toPair ∘ (decode-vec 1) ∘ code-vec ∘ toVec) p
    ≡⟨ cong toPair $ decode-code-vec (toVec p) ⟩
        (toPair ∘ toVec) p
    ≡⟨ toPair-toVec p ⟩
        p
    ≡∎
    where
        dec = decode-pair-inf
        enc = code-pair-inf
    
code-decode-pair-inf : (code-pair-inf ∘ decode-pair-inf) ≈ id {A = ℕ}
code-decode-pair-inf i =
    ≡begin 
        enc (dec i)
    ≡⟨⟩
        (code-vec ∘ toVec ∘ toPair ∘ (decode-vec 1)) i
    ≡⟨ cong code-vec $ toVec-toPair (decode-vec 1 i) ⟩
        (code-vec ∘ (decode-vec 1)) i
    ≡⟨ code-decode-vec 1 i ⟩
        i    
    ≡∎
    where
        dec = decode-pair-inf
        enc = code-pair-inf
    
decode-pair-lemma-inf
    : (i y x : ℕ)
    → decode-pair-inf i ≡ (x , y)
    → y ≤ i
decode-pair-lemma-inf i y x eq = 
    sublemma v eq (decode-vec-lemma 1 i v refl)
    where
        v : Vec ℕ 2
        v = decode-vec 1 i
        sublemma 
            : (v : Vec ℕ 2) 
            → (toPair v ≡ (x , y)) 
            → (All (_≤ i) v)
            → y ≤ i
        sublemma (x ∷ y ∷ []) refl (px All.∷ py All.∷ All.[]) = py

code-pair' : {ζ' : ℕ∞} → ^ (suc∞ ζ') × ℕ → ℕ
code-pair' {fin n'} = code-pair-fin {n'}
code-pair' {∞} = code-pair-inf
        
decode-pair' : {ζ' : ℕ∞} → ℕ → ^ (suc∞ ζ') × ℕ
decode-pair' {fin n'} = decode-pair-fin {n'}
decode-pair' {∞} = decode-pair-inf

decode-code-pair'
    : {ζ' : ℕ∞}
    → (decode-pair' ∘ code-pair') ≈ id {A = ^ (suc∞ ζ') × ℕ}
decode-code-pair' {fin n'} = decode-code-pair-fin {n'}
decode-code-pair' {∞} = decode-code-pair-inf

code-decode-pair'
    : {ζ' : ℕ∞}
    → (code-pair' ∘ decode-pair' {ζ'}) ≈ id {A = ℕ}
code-decode-pair' {fin n'} = code-decode-pair-fin {n'}
code-decode-pair' {∞} = code-decode-pair-inf

decode-pair-lemma'
    : {ζ' : ℕ∞}
    → (i y : ℕ)
    → (x : ^ (suc∞ ζ'))
    → decode-pair' {ζ'} i ≡ (x , y)
    → y ≤ i
decode-pair-lemma' {fin n'} = decode-pair-lemma-fin {n'}
decode-pair-lemma' {∞} = decode-pair-lemma-inf

-- #EXT: most definitions below are duplicate with the ones above,
-- the only difference is that they are instantiated for a fixed μ or ζ
-- at import time.
module WithMuZeta (μ' ζ' : ℕ∞) where
    μ : ℕ∞
    μ = suc∞ μ'

    ζ : ℕ∞
    ζ = suc∞ ζ'

    code-sum : ^ μ ⊎ ℕ → ℕ
    code-sum = code-sum' {μ'}
    decode-sum : ℕ → ^ μ ⊎ ℕ
    decode-sum = decode-sum' {μ'}

    decode-code-sum : decode-sum ∘ code-sum ≈ id
    decode-code-sum = decode-code-sum' {μ'}

    code-decode-sum : code-sum ∘ decode-sum ≈ id
    code-decode-sum = code-decode-sum' {μ'}


    code-pair : ^ ζ × ℕ → ℕ
    code-pair = code-pair' {ζ'}
    decode-pair : ℕ → ^ ζ × ℕ 
    decode-pair = decode-pair' {ζ'}


    decode-code-pair : decode-pair ∘ code-pair ≈ id
    decode-code-pair = decode-code-pair' {ζ'}

    code-decode-pair : code-pair ∘ decode-pair ≈ id
    code-decode-pair = code-decode-pair' {ζ'}

    decode-sum-lemma
        : (i w : ℕ)
        → decode-sum i ≡ inj₂ w
        → w < i
    decode-sum-lemma = decode-sum-lemma' {μ'}

    code-sum-lemma
        : (w : ℕ)
        → w < code-sum (inj₂ w)
    code-sum-lemma w = 
        decode-sum-lemma (code-sum (inj₂ w)) w (decode-code-sum (inj₂ w))

    decode-pair-lemma
        : (i y : ℕ)
        → (x : ^ ζ)
        → decode-pair i ≡ (x , y)
        → y ≤ i
    decode-pair-lemma = decode-pair-lemma' {ζ'}

    code-pair-lemma
        : (y : ℕ)
        → (x : ^ ζ)
        → y ≤ code-pair (x , y)
    code-pair-lemma y x = 
        decode-pair-lemma (code-pair (x , y)) y x (decode-code-pair (x , y))

    decode-sum-pair-lemma
        : (i w y : ℕ)
        → (x : ^ ζ)
        → decode-sum i ≡ inj₂ w
        → decode-pair w ≡ (x , y)
        → y < i
    decode-sum-pair-lemma i w y x eq-i eq-w = ≤-<-trans y≤w w<i
        where
            y≤w : y ≤ w
            y≤w = decode-pair-lemma w y x eq-w
            w<i : w < i
            w<i = decode-sum-lemma i w eq-i
