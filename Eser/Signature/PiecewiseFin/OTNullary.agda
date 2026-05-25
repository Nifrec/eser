-- Module      : Eser.Signature.PiecewiseFin.OTNullary
-- Description : Size of subtype of nullary-constructed terms of OpenTerms w n.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
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

module Eser.Signature.PiecewiseFin.OTNullary
    {μ ζ : ℕ∞}
    (S : Signature μ ζ)
    where

open import Eser.Signature.PiecewiseFin.Definitions {μ} {ζ} S

isNullaryNoArgs 
    : {w : ℕ} 
    → {n : ℕ} 
    → (t : OT w n)
    → IsNullary t
    → n ≡ 0
isNullaryNoArgs {w} {0} (mk-nullary c) p = refl

-- Sublemma of lemma isNullaryWeightLemma below.
-- For isNullaryWeightLemma, either
-- use (t : OT w 0) and Σ[ c ∈ cardToSet μ ] (fin (w ∸ 1) <∞ μ),
-- which has an annoying _∸_ but allows to pattern
-- match t to `mk-nullary c`,
-- xor
-- use (t : OT (ℕ.suc w) 0) and Σ[ c ∈ cardToSet μ ] (fin w <∞ μ),
-- in which case Agda fails to rule out the giveArg case and we don't get c
-- via pattern matching. `getNullaryConstr` then gives c anyway.
getNullaryConstr
    : {w : ℕ} 
    → (t : OT w 0)
    → IsNullary t
    → Σ[ c ∈ cardToSet μ ]( w ≡ ℕ.suc (cardToℕ c) )
getNullaryConstr {w} (mk-nullary c) p = (c , H)
    where
        H : w ≡ ℕ.suc (cardToℕ c)
        H = refl

getNullaryConstrLemma
    : {w : ℕ} 
    → (c : cardToSet μ)
    → (proj₁ $ getNullaryConstr  (mk-nullary c) tt) ≡ c
getNullaryConstrLemma {w} c = refl

isNullaryWeightLemma
    : {w : ℕ} 
    → (t : OT (ℕ.suc w) 0)
    → IsNullary t
    → fin w <∞ μ
isNullaryWeightLemma {w} t p =
    let (c , Sw≡Sc) = getNullaryConstr t p
    in
    let w≡c : fin w ≡ fin (cardToℕ c)
        w≡c = cong fin $ suc-injective Sw≡Sc
    in
    subst (λ x → x <∞ μ) (sym w≡c) (smallerThanCard c)

isNullaryUnderSubst
    : {w : ℕ}
    → {c : cardToSet μ}
    → (p : (ℕ.suc (cardToℕ c) ≡ w))
    → IsNullary (subst (λ x → OT x 0) p (mk-nullary c))
isNullaryUnderSubst refl = tt

isNullaryInhabited
    : {w : ℕ}
    → (H : fin w <∞ μ)
    → OT-Nul (ℕ.suc w) 0
isNullaryInhabited {w} H = 
    let c : cardToSet μ
        c = proj₁ $ cardFrom<∞ H
    in
    let Sc≡Sw : ((ℕ.suc $ cardToℕ c) ≡ ℕ.suc w)
        Sc≡Sw = cong ℕ.suc (proj₂ $ cardFrom<∞ H)
    in
    let t : OpenTerms {μ} {ζ} S (ℕ.suc w) 0
        t = subst (λ x → OpenTerms {μ} {ζ} S x 0) Sc≡Sw (mk-nullary c)
    in
    (t , isNullaryUnderSubst Sc≡Sw)

-- We have to abstract equality of the weights of t and t'
-- into a separate hypothesis H : w ≡ w',
-- since Agda gets stuck in an unification problem otherwise
-- when pattern-matching t and t'; 
-- Agda cannot tell if 
-- ℕ.suc (arity c) ≗ w ≗ ℕ.suc (arity c') has a solution.
-- For this reason, the proof below breaks when trying to replace H by refl.
isNullaryUnique'
    : (wt : Σ[ w ∈ ℕ ](OT w 0))
    → (w't' : Σ[ w ∈ ℕ ](OT w 0))
    → IsNullary (proj₂ wt)
    → IsNullary (proj₂ w't')
    → (H : proj₁ wt ≡ proj₁ w't')
    → wt ≡ w't'
isNullaryUnique' (w , mk-nullary c) (w' , mk-nullary c') p p' H =
    let c≡c' : c ≡ c'
        c≡c' = cardToℕ-injective $ suc-injective H
    in
    cong (λ c → ((ℕ.suc $ cardToℕ c) , mk-nullary c)) c≡c'
    
isNullaryUnique
    : {w : ℕ} 
    → (t t' : OT w 0)
    → IsNullary t
    → IsNullary t'
    → t ≡ t'
isNullaryUnique {w} t t' p p' = 
    let wt≡wt' : (w , t) ≡ (w , t') 
        wt≡wt' = isNullaryUnique' (w , t) (w , t') p p' refl
    in
    openTermsEquality S wt≡wt' 

isNullaryIrrelevant
    : {w n : ℕ}
    → (t : OT w n)
    → (p p' : IsNullary t)
    → p ≡ p'
isNullaryIrrelevant {w} {n} (mk-nullary c) tt tt = refl

OT-Nul-Irrelevant'
    : {w n : ℕ}
    → {t t' : OT w n}
    → (p : IsNullary t)
    → (p' : IsNullary t')
    → t ≡ t'
    → (t , p) ≡ (t' , p')
OT-Nul-Irrelevant' {t = t} p p' refl = 
    cong (λ p → (t , p)) $ isNullaryIrrelevant t p p'
    

OT-Nul-Irrelevant
    : {w n : ℕ}
    → (tp t'p' : OT-Nul w n)
    → tp ≡ t'p'
OT-Nul-Irrelevant {w} {suc n} (t , p) (t' , p') = 
    ⊥-elim $ 1+n≢0 $ isNullaryNoArgs t p

OT-Nul-Irrelevant {w} {0} (t , p) (t' , p') = 
    let t≡t' : t ≡ t'
        t≡t' = isNullaryUnique t t' p p'
    in
    OT-Nul-Irrelevant' p p' t≡t' 

-- Size of the subset of OpenTerms w n that are created with the mk-nullary
-- constructor. They never take any arguments (for n > 0 it is uninhabited)
-- and their weight is 1 + their index in μ (the set of nullary
-- constructors).
Z-Nul' 
    : (μ ζ : ℕ∞)
    → (S : Signature μ ζ)
    → (w n : ℕ)
    → ℕ
Z-Nul' μ ζ S w (suc n)  = 0 -- No nullary constructors take arguments.
Z-Nul' μ ζ S 0 0        = 0 -- All terms have weight at least one.
-- A nullary term with weight `suc w` has index w in `cardToSet μ`.
-- If the latter is ℕ then this term always exists; 
-- but if `cardToSet μ` is `Fin m` then it only exists if `w < m`.
Z-Nul' μ ζ S (suc w) n  = if does ((fin w) <∞? μ) then 1 else 0

Eq-Nul' 
    : (w n : ℕ)
    → Σ[ z ∈ ℕ ] (OT-Nul w n ≃ Fin z)
Eq-Nul' w (suc n) = (0 , ≃-trans equiv (≃-sym fin0))
    where
        equiv : OT-Nul w (ℕ.suc n) ≃ ⊥
        equiv = mk≃' f f⁻¹ invˡ invʳ
            where
            f : OT-Nul w (ℕ.suc n) → ⊥
            f (t , p) = 1+n≢0 $ isNullaryNoArgs t p
            f⁻¹ : ⊥ → OT-Nul w ( ℕ.suc n)
            f⁻¹ ()
            invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
            invˡ {()} {y}
            invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
            invʳ {y} {()}
Eq-Nul' 0 0 = (0 , ≃-trans equiv (≃-sym fin0))
    where
        equiv : OT-Nul 0 0 ≃ ⊥
        equiv = mk≃' f f⁻¹ invˡ invʳ
            where
            f : OT-Nul 0 0 → ⊥
            f (t , _) = noWeightlessTerms S 0 t
            f⁻¹ : ⊥ → OT-Nul 0 0
            f⁻¹ ()
            invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
            invˡ {()} {y}
            invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
            invʳ {y} {()}
Eq-Nul' (suc w) 0 with (fin w <∞? μ)
... | no ¬p = (0 ,  ≃-trans equiv (≃-sym fin0))
    where 
        equiv : OT-Nul (ℕ.suc w) 0 ≃ ⊥
        equiv = mk≃' f f⁻¹ invˡ invʳ
            where
            f : OT-Nul (ℕ.suc w) 0 → ⊥
            f (t , isNullaryT) = ¬p (isNullaryWeightLemma t isNullaryT)
            f⁻¹ : ⊥ → OT-Nul (ℕ.suc w) 0
            f⁻¹ () 
            invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
            invˡ {()} {y}
            invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
            invʳ {y} {()}
... | yes p = (1 , equiv)
    where 
        equiv : OT-Nul (ℕ.suc w) 0 ≃ Fin 1
        equiv = mk≃' f f⁻¹ invˡ invʳ
            where
            f : OT-Nul (ℕ.suc w) 0 → Fin 1
            f _ = Fin.zero
            f⁻¹ : Fin 1 → OT-Nul (ℕ.suc w) 0
            f⁻¹ _ = isNullaryInhabited p 
            invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
            invˡ {Fin.zero} {y} refl = refl
            invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
            invʳ {t} {Fin.zero} refl = OT-Nul-Irrelevant (f⁻¹ Fin.zero) t
