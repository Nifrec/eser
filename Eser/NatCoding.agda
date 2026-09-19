-- Module      : Eser.Signature.NatCoding
-- Description : Encoding and decoding to ℕ of various simple types.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------

{-# OPTIONS --safe #-}

open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum
open import Data.Product
open import Data.Empty
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)
open import Data.Vec
open import Data.Vec.Relation.Unary.All
open import Data.Vec.Relation.Unary.All as All hiding (_∷_)
open import Data.Fin using (Fin ; toℕ ; fromℕ<)
open import Data.Fin.Properties using (toℕ-fromℕ< ; toℕ<n ; fromℕ<-toℕ)
open import Function hiding (_↔_)
--open import Function.Properties.Inverse hiding (refl ; trans ; sym)
open import Function.Consequences.Propositional 
    using (inverseˡ⇒strictlyInverseˡ 
          ; inverseʳ⇒strictlyInverseʳ
          )
--open import Relation.Binary.Structures
--open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Binary.PropositionalEquality.Properties 
    renaming (setoid to mk-≡-setoid)

open import Eser.Aux using 
    ( uip 
    ; _≈_ 
    ; restIsProofIrrel 
    ; double-eq-single-eq
    ; double-eq-never-odd
    ; <?-≮ 
    ; <?-<
    )
open import Eser.Card
open import Eser.Signature.Definitions
open import Eser.Equivalences.Notation
open import Eser.Equivalences.Properties
open import Eser.NewSigStream.EnumVectors
open import Eser.Partitions
open import Eser.Partitions.Properties


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
decode-code-sum-fin {n} x = cases x
    where
        -- Putting the case distinction on x in a subfunction
        -- instead of in decode-code-sum-fin directly
        -- prevents duplication of the following lines:
        -- #EXT: in hindsight, the direct case distinction would have been more
        -- concise and more readable...
        f = code-sum-fin {n}
        f⁻¹ = decode-sum-fin {n}

        cases 
            : (x : Fin n ⊎ ℕ)
            → (f⁻¹ (f x)) ≡ x
        cases (inj₂ x) = 
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
                open DecSumFinImpl {n} (x + n) renaming (cases to dec-cases)
                x+n≮n : x + n ≮ n
                x+n≮n = m+n≮n x n
            
        cases (inj₁ x) = 
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
                open DecSumFinImpl {n} (toℕ x) renaming (cases to dec-cases)
                x<n : toℕ x < n
                x<n = toℕ<n x

module WithMu (μ' : ℕ∞) where
    μ : ℕ∞
    μ = suc∞ μ'

    code-sum : ^ μ ⊎ ℕ → ℕ
    code-sum = {! code-sum-lemma !}
    decode-sum : ℕ → ^ μ ⊎ ℕ
    decode-sum = {!  !}

    decode-sum-lemma
        : (i w : ℕ)
        → decode-sum i ≡ inj₂ w
        → w < i
    decode-sum-lemma i w eq = ?

    decode-code-sum : decode-sum ∘ code-sum ≈ id
    decode-code-sum = ?

    code-decode-sum : code-sum ∘ decode-sum ≈ id
    code-decode-sum = ?

module WithZeta (ζ' : ℕ∞) where
    ζ : ℕ∞
    ζ = suc∞ ζ'

    -- #TODO: (de)code pair depends also on ζ
    -- If ^ ζ is finite then there are only finitely many indices.
    -- Need two lemmas: code ℕ × ℕ and code (Fin n) × ℕ.
    code-pair : ^ ζ × ℕ → ℕ
    code-pair = ?
    decode-pair : ℕ → ^ ζ × ℕ 
    decode-pair = ?

    decode-pair-lemma
        : (i y : ℕ)
        → (x : ^ ζ)
        → decode-pair i ≡ (x , y)
        → y ≤ i
    decode-pair-lemma i y x eq = ?


    decode-code-pair : decode-pair ∘ code-pair ≈ id
    decode-code-pair = ?

    code-decode-pair : code-pair ∘ decode-pair ≈ id
    code-decode-pair = ?


module WithMuZeta (μ' ζ' : ℕ∞) where
    open WithMu μ' public
    open WithZeta ζ' public

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
