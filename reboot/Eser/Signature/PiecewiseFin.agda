-- Module      : Eser.Signature.PiecewiseFin
-- Description : Proof that `OpenTerms w n ≃ Fin z` for some z, for all w n : ℕ.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- Intermediate result towards proving that all term algebras of signatures
-- are enumerable: showing that every set open terms of a given weight
-- and a given number of still-required-arguments
-- is isomorphic to some finite set.
--
-- Strategy:
-- 1. OT 0 n ≃ Fin 0 since there are terms of weight 0.
-- 2. for w = suc ŵ:
--  OT w n ≡ (OT⁰ w n) ⊎ (OTᵉ w n) ⊎ (OTᵃ w n)
--      where 
--          OT⁰ w n are the terms in OT w n made with mk-nullary.
--          OT⁼ w n are the terms in OT w n made with mk-multiary,
--              i.e., constructors without any aguments applied.
--          OTᵃ w n are the terms in OT w n made with giveArg,
--              i.e., constructors with one or more arguments applied.
-- 3. OT⁰ w (suc n) ≃ Fin 0 always, 
--      because nullary constructors don't need arguments. 
--    OT⁰ w 0 ≃ Fin 1 if there are at least w nullary constructors,
--      and OT⁰ w 0 ≃ ⊥ otherwise; 
--      only the term with index w-1 has weight w,
--      but it doesn't exist if the set of nullary constructors
--      is smaller than Fin w.
-- 3. OTᵉ w n ≃ Fin 1 if there are at least w constructors
--      and the constructor with index w-1 has arity n.
--      Otherwise OTᵉ w n ≃ Fin 0
-- 4. showing OTᵃ w n ≃ Fin (żᵃ w n) is the only hard case.
--      How many open terms of the form `giveArg t a`
--      of weight w needing n more arguments exist?
--      Well note the following data is required to build such a term:
--          - weights wₜ and wₐ such that wₐ + wₜ ≡ w.
--              There are w-1 = ŵ such choices (see point 6 below).
--          - A base term t ∈ OT wₜ (suc n) ≃ Fin(ż wₜ n)
--          - An argument a ∈ OT wₐ 0       ≃ Fin(ż wₐ 0)
--      The last two equivalences can be obtained via Well-Founded (ℕ, <)
--      recursion on w when defining the ZTheoremInhab via <-rec;
--      the reasoning is as follows:
--      since both weights are inhabited we must have wₜ ≥ 1 and wₐ ≥ 1, 
--      so if w ≡ wₐ + wₜ then both wₐ < w and wₜ < w must hold. 
--      Consequently, we can make recursive calls with arguments wₐ and wₜ.
-- 5. So define 
--  OTᵃ w n ≔ Σ[(wₜ,wₐ,p) ∈ Splits w](OT wₜ (suc n)) × (OT wₐ 0)
--          ≃ Σ[Fin( ŵ )] Fin(ż wₜ n) × Fin(ż wₐ 0)
-- 6. Here `Splits w` (for any w ≗ suc ŵ) is the set of splits of w into 
--      two non-zero numbers that sum to w.
--      Formally:
--          Splits w ≔ Σ[x ∈ ℕ]Σ[y ∈ ℕ](suc x + suc y ≡ w)
--      Note that x ∈ {0, ..., w-2} ≃ Fin w-1 ≃ Fin ŵ,
--      and choosing an x fixes the only
--      possible choice of y already as 
--          suc y ≡ w - suc x = ŵ - x
--              so
--          y ≡ ŵ - x - 1
--      which has exactly one solution for all x ∈ {0, ..., ŵ-1},
--      if ŵ ≥ 1 and none if ŵ ≡ 0, but then x ∈ ⊥ anyway.
--      Hence the solutions are in bijection to the choice of x ∈ Fin ŵ.

{-# OPTIONS --allow-unsolved-metas #-}

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
open import Eser.Signature.Splits

module Eser.Signature.PiecewiseFin where

--------------------------------------------------------------------------------
-- Theorem: there are finitely many terms of a fixed weight
--
-- I.e., `OpenTerms w n ≃ Fin (z n w)` for all w ∈ ℕ for some z : ℕ → ℕ → ℕ
--------------------------------------------------------------------------------
ZP  : {μ ζ : ℕ∞} 
    → (S : Signature (μ) (ζ))
    → (w : ℕ) 
    → Set
ZP {μ} {ζ} S w = (n : ℕ) → Σ[ z ∈ ℕ ]( OpenTerms {μ} {ζ} S w n ≃ Fin z )

module WithSigAsArg
    {μ ζ : ℕ∞}
    (S : Signature μ ζ)
    where

    OT = OpenTerms {μ} {ζ} S

    IsNullary : {w : ℕ} → {n : ℕ} → OT w n → Set
    IsNullary (mk-nullary _) = ⊤
    IsNullary (mk-multiary _) = ⊥
    IsNullary (giveArg _ _) = ⊥

    IsEmptyMultiary : {w : ℕ} → {n : ℕ} → OT w n → Set
    IsEmptyMultiary (mk-nullary _) = ⊥
    IsEmptyMultiary (mk-multiary _) = ⊤
    IsEmptyMultiary (giveArg _ _) = ⊥

    IsGiveArg : {w : ℕ} → {n : ℕ} → OT w n → Set
    IsGiveArg (mk-nullary _) = ⊥
    IsGiveArg (mk-multiary _) = ⊥
    IsGiveArg (giveArg _ _) = ⊤

    isNullaryNoArgs 
        : {w : ℕ} 
        → {n : ℕ} 
        → (t : OT w n)
        → IsNullary t
        → n ≡ 0
    isNullaryNoArgs {w} {0} (mk-nullary c) p = refl

    -- Sublemma of lemma isNullaryWeight below.
    -- For isNullaryWeight, either
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

    isNullaryWeight
        : {w : ℕ} 
        → (t : OT (ℕ.suc w) 0)
        → IsNullary t
        → fin w <∞ μ
    isNullaryWeight {w} t p =
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

        

    giveArgUnderSubst
        : {w wₐ wₜ : ℕ}
        → {n : ℕ}
        → (p : (ℕ.suc wₐ + ℕ.suc wₜ ≡ w))
        → (t : OpenTerms {μ} {ζ} S (ℕ.suc wₜ) (ℕ.suc n))
        → (a : OpenTerms {μ} {ζ} S (ℕ.suc wₐ) 0)
        → IsGiveArg (subst (λ x → OT x n) p (giveArg t a))
    giveArgUnderSubst refl t a = tt

    OT-Nul : ℕ → ℕ → Set
    OT-Nul w n = Σ[ t ∈ OT w n ] (IsNullary t)

    OT-Mul : ℕ → ℕ → Set
    OT-Mul w n = Σ[ t ∈ OT w n ] (IsEmptyMultiary t)

    OT-Arg : ℕ → ℕ → Set
    OT-Arg w n = Σ[ t ∈ OT w n ] (IsGiveArg t)

    -- Trivial sublemma: OT w n is an Agda-inductive type, and hence the sum
    -- over all of its Agda-constructors of the subsets of the terms
    -- constructed with that constructor.
    ZsubDecompo : (w : ℕ) → (n : ℕ) → OT w n ≃ (OT-Nul w n) ⊎ (OT-Mul w n) ⊎ (OT-Arg w n)
    ZsubDecompo w n = mk≃ {to = to} {from = from} inv
        where 
            to : OT w n → (OT-Nul w n) ⊎ (OT-Mul w n) ⊎ (OT-Arg w n)
            to t@(mk-nullary _) = inj₁ (t , tt)
            to t@(mk-multiary _) = inj₂ $ inj₁ (t , tt)
            to t@(giveArg _ _) = inj₂ $ inj₂ (t , tt)

            from : (OT-Nul w n) ⊎ (OT-Mul w n) ⊎ (OT-Arg w n) → OT w n
            from (inj₁ (t , _)) = t
            from (inj₂ (inj₁ (t , _))) = t
            from (inj₂ (inj₂ (t , _))) = t
            invˡ : Inverseˡ _≡_ _≡_ to from
            invˡ {inj₁ (mk-nullary _ , tt)} {t} refl = refl
            invˡ {inj₂ (inj₁ (mk-multiary _ , tt))} {t} refl = refl
            invˡ {inj₂ (inj₂ (giveArg _ _ , tt))} {t} refl = refl
            invʳ : Inverseʳ _≡_ _≡_ to from
            invʳ {mk-nullary _} {x} refl = refl
            invʳ {mk-multiary _} {x} refl = refl
            invʳ {giveArg _ _} {x} refl = refl
            inv : Inverseᵇ _≡_ _≡_ to from
            inv = (invˡ , invʳ)
 
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

    getNullaryConstrLemma
        : {w : ℕ} 
        → (c : cardToSet μ)
        → (proj₁ $ getNullaryConstr  (mk-nullary c) tt) ≡ c
    getNullaryConstrLemma {w} c = refl

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
        → (t t' : OT-Nul w n)
        → t ≡ t'
    OT-Nul-Irrelevant {w} {suc n} (t , p) (t' , p') = 
        ⊥-elim $ 1+n≢0 $ isNullaryNoArgs t p

    OT-Nul-Irrelevant {w} {0} (t , p) (t' , p') = 
        let t≡t' : t ≡ t'
            t≡t' = isNullaryUnique t t' p p'
        in
        OT-Nul-Irrelevant' p p' t≡t' 

--------------------------------------------------------------------------------
-- Size of subset of nullary-constructed open terms
--------------------------------------------------------------------------------
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
                f (t , isNullaryT) = ¬p (isNullaryWeight t isNullaryT)
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

-- Implementation of the proof for the ZTheorem for the case where w ≥ 1.
-- Submodule that also assumes a given weight w and num-remaining-args n
-- plus the ability to perfrom Well-Founded recursion on w.
module WithArgs
    {μ ζ : ℕ∞}
    (S : Signature μ ζ)
    (w-1 : ℕ)
    (rec : {w' : ℕ} → (w' < ℕ.suc w-1) → ZP {μ} {ζ} S w')
    (n : ℕ) 
    where

    open WithSigAsArg {μ} {ζ} S

    w = ℕ.suc w-1
    Z-Nul = proj₁ $ Eq-Nul' w n
    Eq-Nul = proj₂ $ Eq-Nul' w n 

    Zₜ : (s : Splits w) → (n : ℕ) → ℕ
    Zₜ s n = proj₁ (rec (split<Right w s) (ℕ.suc n))

    Hₜ  : (s : Splits w) 
        → (n : ℕ) 
        → (OT (ℕ.suc $ proj₁ $ proj₂ s) (ℕ.suc n)) ≃ (Fin $ Zₜ s n )
    Hₜ s n = proj₂ (rec (split<Right w s) (ℕ.suc n))

    Zₐ : (s : Splits w) → ℕ
    Zₐ s = proj₁ (rec (split<Left w s) 0)

    Hₐ  : (s : Splits w) 
        → (OT (ℕ.suc (proj₁ s)) 0) ≃ (Fin $ Zₐ s )
    Hₐ s = proj₂ (rec (split<Left w s) 0)

    Eq-split
        : (n : ℕ)
        → (s : Splits w)
        →   (
                (OT (ℕ.suc (proj₁ (proj₂ s))) (ℕ.suc n)) 
                × 
                (OT (ℕ.suc (proj₁ s)) 0)
            )
            ≃ 
            ((Fin $ Zₜ s n ) × (Fin $ Zₐ s ))
    Eq-split n s = ≃-× (Hₜ s n) (Hₐ s) 

    OT-Arg-Unfolded : ℕ → ℕ → Set
    OT-Arg-Unfolded w n = (Σ[ (wₐ , wₜ , p) ∈ (Splits w) ]( 
                       (OT (ℕ.suc wₜ) (ℕ.suc n)) × (OT (ℕ.suc wₐ) 0)))

    -- This needs to be defines for all (w , n)
    -- otherwise we cannot pattern match the input to f
    -- to something of the form `giveArg t a`, since w would be
    -- fixed and Agda can't assume arbitrary wₜ and wₐ if there
    -- is a constraint wₜ + wₐ ≗ w for non-variable w. 
    Eq-Arg-FirstStep : (w n : ℕ) → OT-Arg w n ≃ OT-Arg-Unfolded w n
    Eq-Arg-FirstStep w n = mk≃' f f⁻¹ invˡ invʳ
        where
        f : (OT-Arg w n) → OT-Arg-Unfolded w n
        f (giveArg {suc wₜ} {suc wₐ} t a , tt) = ((wₐ , wₜ , refl) , t , a)
        f (giveArg {ℕ.zero} {wₐ} t a , tt) = ⊥-elim $ noWeightlessTerms S (ℕ.suc n) t
        f (giveArg {wₜ} {ℕ.zero} t a , tt) = ⊥-elim $ noWeightlessTerms S 0 a
        f⁻¹ : OT-Arg-Unfolded w n → (OT-Arg w n)
        f⁻¹ ((wₐ , wₜ , p) , t' , a) = 
            let t = subst (λ x → OT x n) p (giveArg t' a)
            in (t , giveArgUnderSubst p t' a)
        invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
        invˡ {(wₐ , wₜ , refl) , t , a} {ta , isGiveArg} refl = refl
        invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
        invʳ {giveArg {ℕ.zero} {wₐ} t a , tt} {x} p = ⊥-elim $ noWeightlessTerms S (ℕ.suc n) t
        invʳ {giveArg {wₜ} {ℕ.zero} t a , tt} {x} p = ⊥-elim $ noWeightlessTerms S 0 a
        invʳ {giveArg {ℕ.suc wₜ} {ℕ.suc wₐ} t a , tt} {(wₐ , wₜ , refl) , t , a} refl = 
            let H = proj₂ $ f⁻¹ ((wₐ , wₜ , refl) , t , a) in
            ≡begin 
                f⁻¹ ((wₐ , wₜ , refl) , t , a) 
            ≡⟨⟩
                ((giveArg t a) , tt)
            ≡∎

    -- It's easier to compute Z-Arg and prove the equivalence
    -- in one go, than to define Z-Arg beforehand.
    Z-Eq-Arg : Σ[ z ∈ ℕ ]( OT-Arg w n ≃ Fin z)
    Z-Eq-Arg = 
        let getSplit : Fin (splitsSize w) → Splits w
            getSplit = Inverse.from (splitsFin w)
        in
        let
            f : Fin (splitsSize w) → ℕ
            f x = (Zₜ (getSplit x) n) * (Zₐ (getSplit x))
        in
        let Z-Arg : ℕ
            Z-Arg = proj₁ (fin-Σ-fun (splitsSize w) f)
        in
        (Z-Arg , 
        (begin 
            OT-Arg w n
        ≃⟨ ≃-refl ⟩
            (Σ[ t ∈ OT w n ] (IsGiveArg t))
        ≃⟨ Eq-Arg-FirstStep w n ⟩
            (Σ[ (wₐ , wₜ , p) ∈ (Splits w) ]( 
                (OT (ℕ.suc wₜ) (ℕ.suc n)) × (OT (ℕ.suc wₐ) 0)
                )
            )
        ≃⟨ rewr-≃-rightOf-Σ (Eq-split n) ⟩
            (Σ[ s ∈ (Splits w) ]((Fin $ Zₜ s n ) × (Fin $ Zₐ s )))
        ≃⟨ rewr-≃-indexOf-Σ-dep (splitsFin w) ⟩
            (Σ[ x ∈ Fin (splitsSize w) ](
                (Fin $ Zₜ (getSplit x) n ) × (Fin $ Zₐ (getSplit x) )))
        -- Use (Fin a) × (Fin b) ≃ Fin (a * b).
        ≃⟨ rewr-≃-rightOf-Σ (λ x → fin-×-* (Zₜ (getSplit x) n) (Zₐ (getSplit x))) ⟩
            (Σ[ x ∈ Fin (splitsSize w) ](
                (Fin $ (Zₜ (getSplit x) n) * (Zₐ (getSplit x)))))
        ≃⟨ proj₂ (fin-Σ-fun (splitsSize w) f) ⟩
            Fin (proj₁ (fin-Σ-fun (splitsSize w) f) )
        ∎
        ))
        
    Z-Arg : ℕ
    Z-Arg = proj₁ Z-Eq-Arg
    Eq-Arg : OT-Arg w n ≃ Fin Z-Arg
    Eq-Arg = proj₂ Z-Eq-Arg

    Z-Mul : ℕ
    Z-Mul = ?

    Eq-Mul : OT-Mul w n ≃ Fin Z-Mul
    Eq-Mul = ?

    z : ℕ
    z = Z-Nul + Z-Mul + Z-Arg

    zEquiv : OT w n ≃ Fin z
    zEquiv =
        begin 
            OT w n
        ≃⟨ ZsubDecompo w n ⟩
            ((OT-Nul w n) ⊎ (OT-Mul w n) ⊎ (OT-Arg w n))
        ≃⟨ rewr-≃-under-⊎-3 Eq-Nul Eq-Mul Eq-Arg ⟩
            (Fin Z-Nul ⊎ Fin Z-Mul ⊎ Fin Z-Arg)
        ≃⟨ rewr-≃-under-⊎-right (fin-⊎-+ Z-Mul Z-Arg) ⟩
            (Fin Z-Nul ⊎ Fin (Z-Mul + Z-Arg ))
        ≃⟨ fin-⊎-+ Z-Nul (Z-Mul + Z-Arg) ⟩
            Fin (Z-Nul + (Z-Mul + Z-Arg))
        ≃⟨ fin-+-assoc Z-Nul Z-Mul Z-Arg ⟩
            Fin (Z-Nul + Z-Mul + Z-Arg)
        ≃⟨ ≃-refl ⟩
            Fin z
        ∎

-- The main statement is as follows:
ZTheorem 
    : {μ ζ : ℕ∞} 
    → (S : Signature μ ζ)
    → (w : ℕ) 
    → (n : ℕ) 
    → Σ[ z ∈ ℕ ]((OpenTerms {μ} {ζ} S w n) ≃ (Fin z))
ZTheorem {μ} {ζ} S w = <-rec (ZP S) f w
    where
        f : (w : ℕ) → (rec : {w' : ℕ} → w' < w → ZP {μ} {ζ} S w') → ZP {μ} {ζ} S w
        f 0 _ = λ n → (0 , ?) -- #TODO: proof that OT 0 n is always empty.
        f (suc w) rec n = (z , p)
            where
                z = {! ZTheoremProof.z {μ} {ζ} S w rec n !}
                p = {! ZTheoremProof.equiv {μ} {ζ} S w rec n !}


-- Alternative presentation of the ZTheorem: give the sizes of the finite
-- sets as a function z : (w : ℕ) → (n : ℕ) → (<size of OT w n> : ℕ).
-- (The ZTheorem uses WF < recursion on w, so it's more convenient to take w as
-- argument there, rather than nesting it below the Σ[ z ∈ ... ] ...).
Z   : {μ ζ : ℕ∞} 
    → (S : Signature (μ) (ζ))
    → Σ[ z ∈ (ℕ → ℕ → ℕ) ](
        (w : ℕ) → (n : ℕ) → ((OpenTerms {μ} {ζ} S w n) ≃ (Fin $ z w n)))
Z {μ} {ζ} S = (z , p)
    where
        z = λ w → λ n → proj₁ (ZTheorem {μ} {ζ} S w n)
        p = λ w → λ n → proj₂ (ZTheorem {μ} {ζ} S w n)

