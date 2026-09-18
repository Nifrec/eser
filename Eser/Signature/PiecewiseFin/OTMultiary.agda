-- Module      : Eser.Signature.PiecewiseFin.OTMultiary
-- Description : Size of subtype of multiary-constructed terms.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------


{-# OPTIONS --safe #-}

open import Level
open import Data.Bool hiding (_≤_ ; _<_ ; _≤?_)
open import Data.Bool.Properties
open import Data.Nat
open import Data.Nat.Properties
open import Data.Nat.Induction
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
open import Data.Vec 
open import Function
open import Relation.Binary.Reasoning.Syntax
open import Data.Fin.Properties using (fromℕ<-toℕ ; toℕ-fromℕ< ; toℕ-injective)

open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)

open import Eser.Aux
open import Eser.Card
open import Eser.Equivalences.Notation
open import Eser.Equivalences.Properties
open import Eser.Signature.Definitions
open import Eser.Signature.Properties

module Eser.Signature.PiecewiseFin.OTMultiary
    {μ ζ : ℕ∞}
    (S : Signature μ ζ)
    where

open import Eser.Signature.PiecewiseFin.Definitions {μ} {ζ} S

isMultiaryUnderDoubleSubst
    : {w n : ℕ}
    → {c : cardToSet ζ}
    → (p : (ℕ.suc (cardToℕ c) ≡ w))
    → (h : (arity {μ} {ζ} {S} c ≡ n))
    → IsEmptyMultiary (doubleSubst OT p h (mk-multiary {μ} {ζ} {S} c))
isMultiaryUnderDoubleSubst refl refl = tt

getN 
    : {w' : ℕ}
    → (h : fin w' <∞ ζ)
    → ℕ
getN {w'} h = arity {μ} {ζ} {S} $ proj₁ $ cardFrom<∞ h

getMultiaryConstr
    : {w n : ℕ} 
    → (t : OT w n)
    → IsEmptyMultiary t
    → Σ[ c ∈ cardToSet ζ ]( w ≡ ℕ.suc (cardToℕ c) × n ≡ arity {μ} {ζ} {S} c)
getMultiaryConstr {w} {n} (mk-multiary c) p = (c , Hw , Hn)
    where
        Hw : w ≡ ℕ.suc (cardToℕ c)
        Hw = refl
        Hn : n ≡ arity {μ} {ζ} {S} c
        Hn = refl

isMultiaryWeightLemma
    : {w' n : ℕ} 
    → (t : OT (ℕ.suc w') n)
    → IsEmptyMultiary t
    → fin w' <∞ ζ
isMultiaryWeightLemma {w} t p =
    let (c , Sw≡Sc , _) = getMultiaryConstr t p
    in
    let w≡c : fin w ≡ fin (cardToℕ c)
        w≡c = cong fin $ suc-injective Sw≡Sc
    in
    subst (λ x → x <∞ ζ) (sym w≡c) (smallerThanCard c)

isMultiaryNumHolesLemma
    : {w' n : ℕ} 
    → (t : OT (ℕ.suc w') n)
    → (p : IsEmptyMultiary t)
    → n ≡ getN (isMultiaryWeightLemma t p)
isMultiaryNumHolesLemma {w'} {n} t p = 
    let (c , Sw≡Sc , n≡ar) = getMultiaryConstr t p in
    let w'≡c : w' ≡ cardToℕ c
        w'≡c = suc-injective Sw≡Sc
    in
    let h : fin w' <∞ ζ
        h = isMultiaryWeightLemma t p
    in
    let w'≡fromH = sym $ proj₂ $ cardFrom<∞ h
    in
    let c≡fromH : c ≡ (proj₁ $ cardFrom<∞ h)
        c≡fromH = cardToℕ-injective $ trans (sym w'≡c) w'≡fromH
    in
    ≡begin 
        n
    ≡⟨ n≡ar ⟩
        arity {μ} {ζ} {S} c
    ≡⟨ cong (arity {μ} {ζ} {S}) c≡fromH ⟩
        (arity {μ} {ζ} {S} $ proj₁ $ cardFrom<∞ h)
    ≡⟨⟩
        (arity {μ} {ζ} {S} $ proj₁ $ cardFrom<∞ $ isMultiaryWeightLemma t p)
    ≡⟨⟩
        getN (isMultiaryWeightLemma t p)
    ≡∎

isMultiaryNumHolesLemma'
    : {w' n : ℕ} 
    → (t : OT (ℕ.suc w') n)
    → (p : IsEmptyMultiary t)
    → (k : fin w' <∞ ζ)
    → n ≡ getN k
isMultiaryNumHolesLemma' {w'} {n} t p k = 
    let H : isMultiaryWeightLemma t p ≡ k
        H = <∞-irrel (isMultiaryWeightLemma t p) k
    in 
    subst (λ k → n ≡ getN k) H (isMultiaryNumHolesLemma t p)

Eq-Mul' 
    : (w n : ℕ)
    → Σ[ z ∈ ℕ ] (OT-Mul w n ≃ Fin z)
Eq-Mul' 0 n = (0 , ≃-trans equiv (≃-sym fin0))
    where
        equiv : OT-Mul 0 n ≃ ⊥
        equiv = mk≃' f f⁻¹ invˡ invʳ
            where
            f : OT-Mul 0 n → ⊥
            f (t , _) = noWeightlessTerms S n t
            f⁻¹ : ⊥ → OT-Mul 0 n
            f⁻¹ ()
            invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
            invˡ {()} {y}
            invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
            invʳ {y} {()}
Eq-Mul' (suc w') n with (fin w' <∞? ζ)
... | no ¬w'<ζ = (0 ,  ≃-trans equiv (≃-sym fin0))
    where 
        equiv : OT-Mul (ℕ.suc w') n ≃ ⊥
        equiv = mk≃' f f⁻¹ invˡ invʳ
            where
                f : OT-Mul (ℕ.suc w') n → ⊥
                f (t , p) = ¬w'<ζ (isMultiaryWeightLemma t p)
                f⁻¹ : ⊥ → OT-Mul (ℕ.suc w') n
                f⁻¹ () 
                invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
                invˡ {()} {y}
                invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
                invʳ {(y)} {()}
... | yes w'<ζ with (n Data.Nat.≟ (getN w'<ζ))
...     | no ¬n≡arity = (0 ,  ≃-trans equiv (≃-sym fin0))
    where 
        equiv : OT-Mul (ℕ.suc w') n ≃ ⊥
        equiv = mk≃' f f⁻¹ invˡ invʳ
            where
                f : OT-Mul (ℕ.suc w') n → ⊥
                f (t , p) = ¬n≡arity (isMultiaryNumHolesLemma' t p w'<ζ)
                f⁻¹ : ⊥ → OT-Mul (ℕ.suc w') n
                f⁻¹ () 
                invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
                invˡ {()} {y}
                invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
                invʳ {(y)} {()}
...     | yes n≡arity = 
            -- Maybe subst n in output instead of giving it as an arg.
            let (t* , isCenterT*) = OT-Mul-isContr w' w'<ζ -- n≡arity
            in
            let isContrOTM' : isContr (OT-Mul (ℕ.suc w') (getN w'<ζ))
                isContrOTM' = OT-Mul-isContr w' w'<ζ
            in
            let isContrOTM : isContr (OT-Mul (ℕ.suc w') n)
                isContrOTM = subst (λ n → isContr (OT-Mul (ℕ.suc w') n)) 
                                   (sym n≡arity) 
                                   isContrOTM'
            in
            (1 , contr≃Fin1 isContrOTM)
    where
        mk-multiaryWithW&N
            : (w n : ℕ)
            → (c : cardToSet ζ)
            → (w ≡ ℕ.suc (cardToℕ c))
            → (n ≡ arity {μ} {ζ} {S} c)
            → OT-Mul w n
        mk-multiaryWithW&N w n c w≡c n≡ar = 
            let t : OT w n 
                t = doubleSubst OT (sym w≡c) (sym n≡ar) (mk-multiary c)
            in
            (t , isMultiaryUnderDoubleSubst (sym w≡c) (sym n≡ar))

        isMultiaryUnique'
            : (wnt    : Σ[ w ∈ ℕ ](Σ[ n ∈ ℕ ] OT w n))
            → (w'n't' : Σ[ w ∈ ℕ ](Σ[ n ∈ ℕ ] OT w n))
            → IsEmptyMultiary (proj₃ wnt)
            → IsEmptyMultiary (proj₃ w'n't')
            → (Hw : proj₁ wnt  ≡ proj₁ w'n't')
            → (Hn : proj₁₂ wnt ≡ proj₁₂ w'n't')
            → wnt ≡ w'n't'
        isMultiaryUnique' (w , n , mk-multiary c) 
                          (w' , n' , mk-multiary c') 
                          p p' Hw Hn =
            let c≡c' : c ≡ c'
                c≡c' = cardToℕ-injective $ suc-injective Hw
            in
            cong (λ c → ((ℕ.suc $ cardToℕ c) 
                         , arity {μ} {ζ} {S} c 
                         , mk-multiary c)
                 ) c≡c'

        isMultiaryUnique
            : {w n : ℕ} 
            → (t t' : OT w n)
            → IsEmptyMultiary t
            → IsEmptyMultiary t'
            → t ≡ t'
        isMultiaryUnique {w} {n} t t' p p' = 
            let wnt≡wnt' : (w , n , t) ≡ (w , n , t') 
                wnt≡wnt' = isMultiaryUnique' (w , n , t) (w , n , t') p p' refl refl
            in
            openTermsEqualityW&N S wnt≡wnt' 

        -- There is at most one proof that a term is multiary.
        -- So two equal multiary terms share the same proof of multiariness.
        contractMuliarinessProofs
            : {w n : ℕ}
            → {t t' : OT w n}
            → t ≡ t'
            → (p : IsEmptyMultiary t)
            → (p' : IsEmptyMultiary t')
            → (t , p) ≡ (t' , p')
        contractMuliarinessProofs {w} {n} {t} {t} refl p p' = cong (λ p → (t , p)) p≡p'
            where
                isMultiaryIrrelevant 
                    : {w n : ℕ} 
                    → {t : OT w n}
                    → (p p' : IsEmptyMultiary t)
                    → p ≡ p'
                isMultiaryIrrelevant {w} {n} {(mk-multiary c)} tt tt = refl

                p≡p' = isMultiaryIrrelevant {w} {n} {t} p p'

        -- OT-Mul w n is a proposition that is inhabited if and only if
        -- 1. w ≗ suc w'
        --      Weightless terms (w ≡ 0) don't exist.
        -- 2. h : fin w' <∞ ζ 
        --      Otherwise there is no constructor of weight w.
        -- 3. n ≡ ℕ.suc $ arity $ proj₁ $ cardFrom<∞ h
        --      Otherwise it has the wrong number of open argument-holes.
        OT-Mul-isContr
            : (w' : ℕ)
            → (h : fin w' <∞ ζ)
            → isContr ( OT-Mul (ℕ.suc w') (getN h))
        OT-Mul-isContr w' h = (t*p* , isCenterT*)
            where
                -- Constructor of contraction center.
                c* : cardToSet ζ
                c* = proj₁ $ cardFrom<∞ h
                w'≡c* : w' ≡ cardToℕ c*
                w'≡c* = sym $ proj₂ $ cardFrom<∞ h
                -- Term of contraction center.
                t*p* = mk-multiaryWithW&N (ℕ.suc w') (getN h) c* (cong ℕ.suc w'≡c*) refl
                t* = proj₁ t*p*
                p* = proj₂ t*p*
                w = ℕ.suc w'
                isCenterT* : (tp : OT-Mul (ℕ.suc w') (getN h)) → t*p* ≡ tp
                isCenterT* (t , p) = 
                    let t*≡t : t* ≡ t
                        t*≡t = isMultiaryUnique {ℕ.suc w'} {getN h} t* t p* p
                    in
                    contractMuliarinessProofs t*≡t p* p 

