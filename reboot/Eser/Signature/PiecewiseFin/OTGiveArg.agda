-- Module      : Eser.Signature.PiecewiseFin.OTGiveArg
-- Description : Size of subtype of giveArg constructed terms.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
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
open import Eser.Signature.Splits

module Eser.Signature.PiecewiseFin.OTGiveArg
    where


module WithSignature
    {μ ζ : ℕ∞}
    (S : Signature μ ζ)
    where

    open import Eser.Signature.PiecewiseFin.Definitions {μ} {ζ} S
    giveArgUnderSubst
        : {w wₐ wₜ : ℕ}
        → {n : ℕ}
        → (p : (ℕ.suc wₐ + ℕ.suc wₜ ≡ w))
        → (t : OpenTerms {μ} {ζ} S (ℕ.suc wₜ) (ℕ.suc n))
        → (a : OpenTerms {μ} {ζ} S (ℕ.suc wₐ) 0)
        → IsGiveArg (subst (λ x → OT x n) p (giveArg t a))
    giveArgUnderSubst refl t a = tt

    -- Submodule that also assumes a given weight w and num-remaining-args n
    -- plus the ability to perfrom Well-Founded recursion on w.
    module AlsoWithW-1&Rec&N
        (w-1 : ℕ)
        (rec : {w' : ℕ} → (w' < ℕ.suc w-1) → ZP w')
        (n : ℕ) 
        where

        w = ℕ.suc w-1

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
