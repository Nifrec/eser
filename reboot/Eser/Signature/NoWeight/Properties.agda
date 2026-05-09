-- Module      : Eser.Signature.NoWeights
-- Description : Properties of the NoWeight representation of open terms.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- Properties shown:
-- 1. Decidable equality between open terms.
-- 2. Equivlance to the weight-annotated representation to open terms.

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

open import Eser.Card
open import Eser.Signature.Definitions
open import Eser.Signature.MainTheorem
open import Eser.Signature.NoWeight.Definitions
open import Eser.Equivalences
open import Eser.Aux

module Eser.Signature.NoWeight.Properties where

-- #TODO: move to other file when done.
module SigmaCasts {I : Set} {A : I → Set} where

    projcast
        : (i : I)
        → (x : Σ[ i ∈ I ] A i)
        → (proj₁ x ≡ i)
        → A i
    projcast i x refl = proj₂ x

    -- projcast preserves propositional equalities.
    projcast-≡
        : (i : I)
        → (x y : Σ[ i ∈ I ] A i)
        → (Hx : proj₁ x ≡ i)
        → (Hy : proj₁ y ≡ i)
        → x ≡ y
        → _≡_ {A = A i} (projcast i x Hx) (projcast i y Hy)
    projcast-≡ i x y refl refl refl = refl

module _ {μ ζ : ℕ∞} (S : Signature μ ζ) where
    private
        CNW : Set
        CNW = ClosedTermsNW {μ} {ζ} S

        OT : ℕ → ℕ → Set
        OT = OpenTerms {μ} {ζ} S

        OTNW : ℕ → Set
        OTNW = OpenTermsNW {μ} {ζ} S

    -- Equality between open terms is decidable.
    decEquality : {n : ℕ} → (t t' : OTNW n) → Relation.Nullary.Dec (t ≡ t')
    decEquality {n} (mk-nullary-nw c) (mk-nullary-nw c') with cardToDecidableEq μ c c'
    ... | yes refl = yes refl
    ... | no c≢c' = no λ { refl → c≢c' refl}
    decEquality {n} (mk-nullary-nw c) (giveArg-nw t' t'') = no λ { () }
    decEquality {n} t@(mk-multiary-nw c) t' = ans 
        where
            lemma 
                : {n' : ℕ}
                → (t' : OTNW n')
                → n ≡ n'
                → Relation.Nullary.Dec (_≡_ {A = Σ[ n ∈ ℕ ](OTNW n)} 
                                        (n , mk-multiary-nw c) (n' , t'))
            lemma (mk-multiary-nw c') n≡n' with cardToDecidableEq ζ c c'
            ... | yes refl = yes refl
            ... | no c≢c' = no λ { refl → c≢c' refl}
            lemma (giveArg-nw t' t'') n≡n' = no λ { () }

            ans : Relation.Nullary.Dec (t ≡ t')
            ans with lemma t' refl
            ... | yes refl = yes refl
            ... | no pairsIneq = no λ {refl → pairsIneq refl}

    decEquality {n} (giveArg-nw t t₁) (mk-nullary-nw c) = no λ { () }
    decEquality {n} (giveArg-nw t t₁) (mk-multiary-nw c) = no λ { () }
    decEquality {n} (giveArg-nw t a) (giveArg-nw t' a') = ans
        where
            yesIfBothSubterms 
                : {t t' : OTNW (ℕ.suc n)} 
                → {a a' : OTNW 0}
                → (Relation.Nullary.Dec (t ≡ t'))
                → (Relation.Nullary.Dec (a ≡ a'))
                → Relation.Nullary.Dec (giveArg-nw t a ≡ giveArg-nw t' a')
            yesIfBothSubterms (yes refl) (yes refl) = yes refl
            yesIfBothSubterms (yes refl) (no a≢a') = no λ { refl → a≢a' refl }
            yesIfBothSubterms (no t≢t') _ = no λ { refl → t≢t' refl }

            ans = yesIfBothSubterms (decEquality {ℕ.suc n} t t')
                              (decEquality {0} a a')

    ----------------------------------------------------------------------------
    -- Recomputing the weights
    --
    -- The weights are really just annotations.
    -- Every term has exacly one weight.
    -- So we obtain a bijection between OpenTermsNW and OpenTerms
    ----------------------------------------------------------------------------

    -- Weights are computed the same way as the indices in OpenTerms.
    weight : {n : ℕ} → OTNW n → ℕ
    weight (mk-nullary-nw c) = (ℕ.suc $ cardToℕ c)
    weight (mk-multiary-nw c) = (ℕ.suc $ cardToℕ c)
    weight (giveArg-nw t a) = weight a + weight t

    -- The weight function allows to embed OpenTermsNW into OpenTerms,
    -- and the forgetful function gives an inverse map to it.
    forgetWeight : {w n : ℕ} → OT w n → OTNW n
    forgetWeight {w} {n} (mk-nullary c) = mk-nullary-nw c
    forgetWeight {w} {n} (mk-multiary c) = mk-multiary-nw c
    forgetWeight {w} {n} (giveArg t a) = giveArg-nw t' a'
        where
            t' = forgetWeight t
            a' = forgetWeight a

    -- Uncurried version of the above.
    forgetWeight' : {n : ℕ} → Σ[ w ∈ ℕ ](OT w n) → OTNW n
    forgetWeight' {n} (w , t) = forgetWeight {w} {n} t

    addWeight : {n : ℕ} → OTNW n → Σ[ w ∈ ℕ ](OT w n)
    addWeight {n} t@(mk-nullary-nw c) = (weight t , mk-nullary c)
    addWeight {n} t@(mk-multiary-nw c) = (weight t , mk-multiary c)
    addWeight {n} t@(giveArg-nw t₀ a) = (wₐ + wₜ₀ , giveArg t₀' a')
        where
            wₜ₀ = proj₁ $ addWeight t₀
            t₀' = proj₂ $ addWeight t₀
            wₐ = proj₁ $ addWeight {0} a
            a' = proj₂ $ addWeight {0} a

    proj₁AddWeight
        : {n : ℕ}
        → (proj₁ ∘ addWeight {n}) ≈ weight {n}
    proj₁AddWeight {n} (mk-nullary-nw c) = refl
    proj₁AddWeight {n} (mk-multiary-nw c) = refl
    proj₁AddWeight {n} (giveArg-nw t a) = 
        ≡begin 
            (proj₁ $ addWeight $ giveArg-nw t a)
        ≡⟨⟩
            (proj₁ $ addWeight a) + (proj₁ $ addWeight t)
        ≡⟨ cong (λ w → (proj₁ $ addWeight a) + w) (proj₁AddWeight t) ⟩
            (proj₁ $ addWeight a) + weight t
        ≡⟨ cong (λ w → w + weight t) (proj₁AddWeight a) ⟩
            weight a + weight t
        ≡⟨⟩
            weight (giveArg-nw t a)
        ≡∎

    weightRecover
        : {w n : ℕ}
        → (t : OT w n)
        → weight (forgetWeight' {n} (w , t)) ≡ w
    weightRecover {w} {n} t = ?

    -- #TODO: move to properties-of-equivalences:
    ≃-curry
        : {I : Set}
        → {A B : I → Set}
        → (H : (Σ[ i ∈ I ] A i) ≃ (Σ[ i ∈ I ] B i))
        → ((proj₁ ∘ (≃-to H)) ≈ proj₁) -- ^ The equivalence preserves the i.
        → (i : I) → A i ≃ B i
    ≃-curry {I} {A} {B} H p i = ans
        where
            ans : A i ≃ B i
            ans = mk≃' f f⁻¹ invˡ invʳ
                where
                α = ≃-to H
                α⁻¹ = ≃-from H
                -- Because of inversity, the inverse must also preserve indices.
                p⁻¹ : ((proj₁ ∘ α⁻¹) ≈ proj₁)
                p⁻¹ (i , b) = 
                    ≡begin 
                        (proj₁ ∘ α⁻¹) (i , b)
                    ≡⟨ sym $ p (α⁻¹ (i , b)) ⟩
                        (proj₁ ∘ α ∘ α⁻¹) (i , b)
                    ≡⟨ cong proj₁ $ ≃-toFrom H (i , b) ⟩
                        i
                    ≡∎


                f : A i → B i
                f a = subst (λ j → B j) (p (i , a)) (proj₂ (α (i , a)))
                f⁻¹ : B i → A i
                f⁻¹ b = subst (λ j → A j) (p⁻¹ (i , b)) (proj₂ (α⁻¹  (i , b)))
                --invˡ : {a : A i} → {b : B i} → (f⁻¹ a ≡ b) 
                --    → (p : proj₁ (α (i , a)) ≡ i) 
                --    → (p⁻¹ : proj₁ (α⁻¹ (i , b) ≡ i) 
                --    → f a ≡ b 
                --meh : (a : A i) → (p : proj₁ (α (i , a)) ≡ i) 
                --    → f⁻¹ (subst (λ j → B j) p (proj₂ (α (i , a)))) ≡ (f⁻¹ (proj₂ (α (i , a))))
                --meh a refl = ?

                invˡ : Inverseˡ _≡_ _≡_ f f⁻¹
                invˡ {a} {b} refl = 
                    ≡begin 
                        f (f⁻¹ a)
                    ≡⟨⟩
                        f (subst (λ j → A j) (p⁻¹ (i , a)) (proj₂ (α⁻¹ (i , a))))
                    ≡⟨ ? ⟩
                        a
                    ≡∎
                    
                invʳ : Inverseʳ _≡_ _≡_ f f⁻¹
                invʳ {y} {x} refl = ?
            

    -- Theorem: the open terms with and without weights are the same.
    -- Implementation note: this is hard to prove directly,
    -- because the inversity proof 
    -- in the the giveArg t a case we would like to make recursive call on
    -- t. But if `giveArg t a` has n holes, then t has `ℕ.suc n` holes,
    -- while inv̂ˡ would have n hardcoded, and a top-level recursive call
    -- to OTequiv fails because ℕ.suc n is not smaller than n.
    -- The solution is to prove that 
    -- (1) (Σ[n∈ℕ] OTWN n) ≃ (Σ[n∈ℕ]Σ[w∈ℕ] OT w n).
    -- (2) that this bijection acts as the idenity on the first projections.
    OTequiv
        : (n : ℕ) 
        → (OTNW n) ≃ (Σ[ w ∈ ℕ ] (OT w n))

    OTequiv-uncurried :
        Σ[ n ∈ ℕ ](OTNW n) ≃ Σ[ n ∈ ℕ ](Σ[ w ∈ ℕ ] OT w n)

    -- Uncurried versions of addWeight and forgetWeight
    α : Σ[ n ∈ ℕ ](OTNW n) → Σ[ n ∈ ℕ ](Σ[ w ∈ ℕ ] OT w n)
    α (n , t) = (n , addWeight {n} t)
    ϕ : Σ[ n ∈ ℕ ](Σ[ w ∈ ℕ ] OT w n) → Σ[ n ∈ ℕ ](OTNW n) 
    ϕ (n , w , t) = (n , forgetWeight {w} {n} t)

    OTequiv-uncurried = mk≃' α ϕ invˡ invʳ where
        RHS : Set
        RHS = Σ[ n ∈ ℕ ](Σ[ w ∈ ℕ ] OT w n)
        -- Agda fails to infer the underlying types when only writing 'proj₂'.
        RHS-proj₂ = proj₂ {A = ℕ} {B = λ n → Σ[ w ∈ ℕ ] OT w n}


        -- #TODO: fix termination by WF recursion on weights or so.
        -- wₐ < w and wₜ < w are easy to prove.
        invˡ : Inverseˡ _≡_ _≡_ α ϕ
        invˡ {n , w , mk-nullary c} {y} refl = refl
        invˡ {n , w , mk-multiary c} {y} refl = refl
        invˡ {n , w , giveArg {wₜ} {wₐ} t a} {y} refl = 
            let H : _≡_ {A = RHS} (α (ϕ (n , wₐ + wₜ , giveArg t a))) 
                                  (n , wₐ + wₜ , giveArg t a)
                H = 
                    ≡begin 
                        α (ϕ (n , wₐ + wₜ , giveArg t a))
                    ≡⟨⟩ -- Unfold ϕ
                        α (n , giveArg-nw (forgetWeight' (wₜ , t)) (forgetWeight' (wₐ , a)))
                    ≡⟨⟩ -- Unfold α
                        (n , (wₐ' + wₜ' , giveArg t' a'))
                    ≡⟨⟩
                        giveArg$ (n , wₜ' , t') (wₐ' , a')
                    ≡⟨ cong (λ x → giveArg$ x (wₐ' , a')) t-rec' ⟩
                        giveArg$ (n , wₜ , t) (wₐ' , a')
                    ≡⟨⟩
                        (n , wₐ' + wₜ , giveArg t a')
                    ≡⟨⟩
                        giveArg# n (wₜ , t) (0 , wₐ' , a') refl
                    ≡⟨ cong (λ y → giveArg# n (wₜ , t) (0 , y) refl) a-rec' ⟩
                       (n , wₐ + wₜ , giveArg t a) 
                    ≡∎
            in H
                
            --   (n , giveArg*** n 
            --        ((ℕ.suc n , wₜ' , t') , refl {x = ℕ.suc n})
            --        ((0       , wₐ' , a') , refl {x = 0})
            --        )
            --        --(proj₂ {B = λ n → Σ[ w ∈ ℕ ] OT w n} (ℕ.suc n , wₜ' , t')) 
            --        --(proj₂ {B = λ n → Σ[ w ∈ ℕ ] OT w n} (0 , wₐ' , a')))
            ----≡⟨ cong₂ (λ x y → (n , giveArg*** n x y))
            ----            {! check-t-tuple!} ?
            ----              --({!cong (λ x → (x , refl)) $ sym t-rec!}) 
            ----              --({!cong (λ y → (y , refl)) $ sym a-rec!}) 
            ----    ⟩
            --≡⟨ subst (λ x → (n , giveArg*** n 
            --                        ((ℕ.suc n , wₜ' , t') , refl {x = ℕ.suc n}) 
            --                        ((0       , wₐ' , a') , refl {x = 0}))
            --                ≡ 
            --                (n , giveArg*** n x ((0       , wₐ' , a') , refl {x = 0})))
            --            {! check-t-tuple !}
            --            refl
            --              --({!cong (λ x → (x , refl)) $ sym t-rec!}) 
            --              --({!cong (λ y → (y , refl)) $ sym a-rec!}) 
            --    ⟩
            ----≡⟨ doubleSubst 
            ----    (λ x y → (n , giveArg** n (ℕ.suc n , wₜ' , t') (0 , wₐ' , a') refl refl) 
            ----             ≡ 
            ----             (n , giveArg** n x y refl refl)
            ----    )
            ----              (sym t-rec) 
            ----              (sym a-rec) 
            ----              refl
            ----    ⟩
            --   (n , giveArg*** n 
            --        ((ℕ.suc n , wₜ , t) , refl)
            --        ((0       , wₐ' , a') , refl)
            --        )
            --   ≡⟨ ? ⟩
                   
            --   (n , giveArg*** n 
            --        ((ℕ.suc n , wₜ , t) , refl)
            --        ((0       , wₐ , a) , refl)
            --        )
            --   --(n , giveArg** n 
            --   --     (ℕ.suc n , wₜ , t)
            --   --     (0       , wₐ , a)
            --   --     refl
            --   --     refl
            --   --     )
            
            where
                wₜ' : ℕ
                wₜ' = (proj₁ $ addWeight $ forgetWeight' (wₜ , t)) 
                t' : OT wₜ' (ℕ.suc n)
                t' = (proj₂ $ addWeight $ forgetWeight' (wₜ , t)) 
                wₐ' : ℕ
                wₐ' = (proj₁ $ addWeight $ forgetWeight' (wₐ , a)) 
                a' : OT wₐ' 0
                a' = (proj₂ $ addWeight $ forgetWeight' (wₐ , a)) 

                t-rec : α (ϕ (ℕ.suc n , wₜ , t)) ≡ (ℕ.suc n , wₜ , t)
                t-rec = invˡ {(ℕ.suc n , wₜ , t)} {ϕ (ℕ.suc n , wₜ , t)} refl

                check-wₜ : (proj₁ $ proj₂ $ α $ ϕ (ℕ.suc n , wₜ , t)) ≡ wₜ'
                check-wₜ = refl

                check-t :  (proj₂ $ proj₂ $ α $ ϕ (ℕ.suc n , wₜ , t)) ≡ t'
                check-t =  refl

                ---- When not giving the base type, it type checks.
                ---- But then it probably takes the wrong base type,
                ---- I guess the weaker: Σ[ x ∈ RHS ] (ℕ.suc n ≡ ℕ.suc n)
                --check-t-tuple : _≡_ {A = Σ[ x ∈ RHS ] (proj₁ x ≡ ℕ.suc n)}
                --                ((ℕ.suc n , wₜ' , t') , refl {x = ℕ.suc n}) 
                --                ((ℕ.suc n , wₜ , t) , refl {x = ℕ.suc n})
                --check-t-tuple = {! cong (λ x → (x , refl {x = ℕ.suc n})) t-rec !}

                check-t-tuple : _≡_ {A = RHS} (ℕ.suc n , wₜ' , t') (ℕ.suc n , wₜ , t)
                check-t-tuple = t-rec

                t-rec' : _≡_ {A = Σ[ n ∈ ℕ ] Σ[ wₜ ∈ ℕ ] OT wₜ (ℕ.suc n)}
                   (n , wₜ' , t') (n , wₜ , t) 
                t-rec' = projcast-t-≡ n 
                                      (ℕ.suc n , wₜ' , t') 
                                      (ℕ.suc n , wₜ , t) 
                                      refl refl t-rec
                    where
                        projcast-t
                            : (n : ℕ)
                            → (x : Σ[ i ∈ ℕ ] Σ[ w ∈ ℕ ] OT w i)
                            → (proj₁ x ≡ ℕ.suc n)
                            → Σ[ i ∈ ℕ ] Σ[ w ∈ ℕ ] OT w (ℕ.suc i)
                        projcast-t n nwt refl = (n , proj₂ nwt)

                        projcast-t-≡
                            : (n : ℕ)
                            → (x y : Σ[ i ∈ ℕ ] Σ[ w ∈ ℕ ] OT w i)
                            → (Hx : proj₁ x ≡ ℕ.suc n)
                            → (Hy : proj₁ y ≡ ℕ.suc n)
                            → x ≡ y
                            → _≡_ {A = Σ[ i ∈ ℕ ] Σ[ w ∈ ℕ ] OT w (ℕ.suc i)}
                                (projcast-t n x Hx)
                                (projcast-t n y Hy)
                        projcast-t-≡ n x y refl refl refl = refl

                        t-tuple : Σ[ n ∈ ℕ ] Σ[ wₜ ∈ ℕ ] OT wₜ (ℕ.suc n)
                        t-tuple = projcast-t n (ℕ.suc n , wₜ , t) refl

                        t'-tuple : Σ[ n ∈ ℕ ] Σ[ wₜ ∈ ℕ ] OT wₜ (ℕ.suc n)
                        t'-tuple = projcast-t n (ℕ.suc n , wₜ' , t') refl

                    --projcast i x refl = proj₂ x
                    --    open SigmaCasts {I = ℕ} {A = λ n → Σ[ w ∈ ℕ ] OT w n} 
                    --    t-tuple : Σ[ wₜ ∈ ℕ ] OT wₜ (ℕ.suc n)
                    --    t-tuple = projcast (ℕ.suc n) (ℕ.suc n , wₜ , t) refl
                    ---- cong (λ x → (n ,  proj₂ x)) check-t-tuple

                a-rec : α (ϕ (0 , wₐ , a)) ≡ (0 , wₐ , a)
                a-rec = invˡ {(0 , wₐ , a)} {ϕ (0 , wₐ , a)} refl

                check-wₐ : (proj₁ $ proj₂ $ α $ ϕ (0 , wₐ , a)) ≡ wₐ'
                check-wₐ = refl

                check-a :  (proj₂ $ proj₂ $ α $ ϕ (0 , wₐ , a)) ≡ a'
                check-a =  refl

                wₜ-equiv : wₜ' ≡ wₜ
                wₜ-equiv = cong (proj₁ ∘ proj₂) t-rec
                wₐ-equiv : wₐ' ≡ wₐ
                wₐ-equiv = cong (proj₁ ∘ proj₂) a-rec

                giveArg*
                    : (n : ℕ)
                    → Σ[ wₜ ∈ ℕ ] OT wₜ (ℕ.suc n)
                    → Σ[ wₐ ∈ ℕ ] OT wₐ 0
                    → Σ[ w ∈ ℕ ] OT w n
                giveArg* n (wₜ , t) (wₐ , a) = (wₐ + wₜ , giveArg t a)

                giveArg**
                    : (n : ℕ)
                    → (nwt : RHS)
                    → (nwa : RHS)
                    → proj₁ nwt ≡ ℕ.suc n
                    → proj₁ nwa ≡ 0
                    → Σ[ w ∈ ℕ ] OT w n
                giveArg** n (ℕ.suc n , wₜ , t) (0 , wₐ , a) refl refl = (wₐ + wₜ , giveArg t a)

                giveArg***
                    : (n : ℕ)
                    → (nwtp : Σ[ x ∈ RHS ] (proj₁ x ≡ ℕ.suc n))
                    → (nwap : Σ[ y ∈ RHS ] (proj₁ y ≡ 0))
                    → Σ[ w ∈ ℕ ] OT w n
                giveArg*** n ((ℕ.suc n , wₜ , t), refl) ((0 , wₐ , a), refl) = (wₐ + wₜ , giveArg t a)

                giveArg$
                    : (nwt : Σ[ n ∈ ℕ ] Σ[ wₜ ∈ ℕ ] OT wₜ (ℕ.suc n))
                    → (wa : Σ[ wₐ ∈ ℕ ] OT wₐ 0 )
                    → RHS
                giveArg$ (n , wₜ , t) (wₐ , a) = (n , wₐ + wₜ , giveArg t a)

                giveArg#
                    : (n : ℕ)
                    → (wt : Σ[ wₜ ∈ ℕ ] OT wₜ (ℕ.suc n))
                    → (mwa : Σ[ m ∈ ℕ ](Σ[ wₐ ∈ ℕ ] OT wₐ m ))
                    → proj₁ mwa ≡ 0
                    → RHS
                giveArg# n (wₜ , t) (0 , wₐ , a) refl = (n , wₐ + wₜ , giveArg t a)

                open SigmaCasts {I = ℕ} {A = λ n → Σ[ w ∈ ℕ ] OT w n} 
                a-rec' : _≡_ {A = Σ[ w ∈ ℕ ] OT w 0} (wₐ' , a') (wₐ , a)
                a-rec' = projcast-≡ 0 (0 , wₐ' , a') (0 , wₐ , a) refl refl a-rec

                -- doubleSubst (λ x y → giveArg* n x y) (cong proj₂ t-rec) (cong proj₂ a-rec) refl

                    
                --t-equiv : (wₜ' , t') ≡ (wₜ , t)
                --t-equiv = cong proj₂ t-rec

            --≡begin 
            --    addWeight (forgetWeight' (wₐ + wₜ , giveArg t a))
            --≡⟨⟩
            --    addWeight (giveArg-nw (forgetWeight' (wₜ , t)) 
            --                          (forgetWeight' (wₐ , a))
            --              )
            --≡⟨⟩
            --    ((proj₁ $ addWeight aNW) + (proj₁ $ addWeight tNW) , giveArg t' a')
            --≡⟨ ? ⟩
            --    -- #TODO: use H above. Also make a Hₐ.
            --    -- Second projections should use substitutions...
            --    -- Maybe prove strict inversity.
            --    -- **Or prove injectivity & surjectivity.**
            --    (wₐ' + wₜ' , giveArg t' a' )
            --≡⟨ ? ⟩
            --    (wₐ + wₜ , giveArg t a) 
            --≡∎
        --    where
        --        tNW : OTNW (ℕ.suc n)
        --        tNW = forgetWeight' (wₜ , t) 
        --        aNW : OTNW 0
        --        aNW = forgetWeight' (wₐ , a) 
                --t-rec : (wₜ , t) ≡ (wₜ' , t')
                --t-rec = invˡ refl
                --H : wₜ' ≡ wₜ
                --H = trans (proj₁AddWeight $ forgetWeight' (wₜ , t)) (weightRecover t)
        invʳ : Inverseʳ _≡_ _≡_ α ϕ
        invʳ {x} {y} refl = ?
        --invʳ {mk-nullary-nw c} {x} refl = refl
        --invʳ {mk-multiary-nw c} {x} refl = refl
        --invʳ {giveArg-nw t a} {x} refl = {! !}

    --OTequiv {n} = mk≃' addWeight forgetWeight' invˡ invʳ
    --    where
    --    invˡ : Inverseˡ _≡_ _≡_ addWeight forgetWeight'
    --    invˡ {w , mk-nullary c} {y} refl = refl
    --    invˡ {w , mk-multiary c} {y} refl = refl
    --    invˡ {w , giveArg {wₜ} {wₐ} t a} {y} refl = 
    --        let t-rec = invˡ {(wₜ , t)} {forgetWeight' (wₜ , t)} refl
    --        in
    --        ≡begin 
    --            addWeight (forgetWeight' (wₐ + wₜ , giveArg t a))
    --        ≡⟨⟩
    --            addWeight (giveArg-nw (forgetWeight' (wₜ , t)) 
    --                                  (forgetWeight' (wₐ , a))
    --                      )
    --        ≡⟨⟩
    --            ((proj₁ $ addWeight aNW) + (proj₁ $ addWeight tNW) , giveArg t' a')
    --        ≡⟨ ? ⟩
    --            -- #TODO: use H above. Also make a Hₐ.
    --            -- Second projections should use substitutions...
    --            -- Maybe prove strict inversity.
    --            -- **Or prove injectivity & surjectivity.**
    --            (wₐ' + wₜ' , giveArg t' a' )
    --        ≡⟨ ? ⟩
    --            (wₐ + wₜ , giveArg t a) 
    --        ≡∎
    --        where
    --            tNW : OTNW (ℕ.suc n)
    --            tNW = forgetWeight' (wₜ , t) 
    --            aNW : OTNW 0
    --            aNW = forgetWeight' (wₐ , a) 
    --            wₜ' : ℕ
    --            wₜ' = (proj₁ $ addWeight $ forgetWeight' (wₜ , t)) 
    --            t' : OT wₜ' (ℕ.suc n)
    --            t' = (proj₂ $ addWeight $ forgetWeight' (wₜ , t)) 
    --            wₐ' : ℕ
    --            wₐ' = (proj₁ $ addWeight $ forgetWeight' (wₐ , a)) 
    --            a' : OT wₐ' 0
    --            a' = (proj₂ $ addWeight $ forgetWeight' (wₐ , a)) 

    --            --t-rec : (wₜ , t) ≡ (wₜ' , t')
    --            --t-rec = invˡ refl
    --            H : wₜ' ≡ wₜ
    --            H = trans (proj₁AddWeight $ forgetWeight' (wₜ , t)) (weightRecover t)
    --        --where
    --        --    t' = forgetWeight' (wₜ , t)
    --        --    (wₜ'' , t'') = addWeight t'
                
    --            --P₁AWₜ = proj₁ $ addWeight t
    --            --t' = proj₂ $ addWeight t
    --            --P₁AWₐ = proj₁ $ addWeight {0} a
    --            --a' = proj₂ $ addWeight {0} a
    --    invʳ : Inverseʳ _≡_ _≡_ addWeight forgetWeight'
    --    invʳ {mk-nullary-nw c} {x} refl = refl
    --    invʳ {mk-multiary-nw c} {x} refl = refl
    --    invʳ {giveArg-nw t a} {x} refl = {! !}

    OTequiv = ≃-curry {ℕ} {OTNW} {λ n → Σ[ w ∈ ℕ ] OT w n} OTequiv-uncurried H
        where
            H : (x : Σ[ n ∈ ℕ ] OTNW n) → (proj₁ (α x) ≡ proj₁ x)
            H (n , t) = refl

-- Corollary: the no-weight closed terms of a signature can be enumerated,
-- because the weight-annotated closed terms can.
infTermAlgEnumNW
    : {μ ζ : ℕ∞}
    → (S : Signature (suc∞ μ) (suc∞ ζ))
    → (ClosedTermsNW {suc∞ μ} {suc∞ ζ} S) ≃ ℕ
infTermAlgEnumNW {μ} {ζ} S = ≃-trans CTNW≃AT AT≃ℕ
    where
        μ' = suc∞ μ
        ζ' = suc∞ ζ
        CTNW≃AT : ClosedTermsNW {μ'} {ζ'} S ≃ AllTerms {μ'} {ζ'} S
        CTNW≃AT = OTequiv {μ'} {ζ'} S 0

        AT≃ℕ : AllTerms {μ'} {ζ'} S ≃ ℕ
        AT≃ℕ = infTermAlgEnum {μ} {ζ} S
