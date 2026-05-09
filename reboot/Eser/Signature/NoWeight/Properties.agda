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

    OTequiv-curried :
        Σ[ n ∈ ℕ ](OTNW n) ≃ Σ[ n ∈ ℕ ](Σ[ w ∈ ℕ ] OT w n)

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
            

    OTequiv = ≃-curry {ℕ} {OTNW} {λ n → Σ[ w ∈ ℕ ] OT w n} OTequiv-curried ?

    OTequiv-curried = mk≃' α ϕ invˡ invʳ where
        -- Uncurried versions of addWeight and forgetWeight
        α : Σ[ n ∈ ℕ ](OTNW n) → Σ[ n ∈ ℕ ](Σ[ w ∈ ℕ ] OT w n)
        α (n , t) = (n , addWeight {n} t)
        ϕ : Σ[ n ∈ ℕ ](Σ[ w ∈ ℕ ] OT w n) → Σ[ n ∈ ℕ ](OTNW n) 
        ϕ (n , w , t) = (n , forgetWeight {w} {n} t)

        invˡ : Inverseˡ _≡_ _≡_ α ϕ
        invˡ {x} {y} refl = ?
        --invˡ {w , mk-nullary c} {y} refl = refl
        --invˡ {w , mk-multiary c} {y} refl = refl
        --invˡ {w , giveArg {wₜ} {wₐ} t a} {y} refl = 
        --    let t-rec = invˡ {(wₜ , t)} {forgetWeight' (wₜ , t)} refl
        --    in
        --    ≡begin 
        --        addWeight (forgetWeight' (wₐ + wₜ , giveArg t a))
        --    ≡⟨⟩
        --        addWeight (giveArg-nw (forgetWeight' (wₜ , t)) 
        --                              (forgetWeight' (wₐ , a))
        --                  )
        --    ≡⟨⟩
        --        ((proj₁ $ addWeight aNW) + (proj₁ $ addWeight tNW) , giveArg t' a')
        --    ≡⟨ ? ⟩
        --        -- #TODO: use H above. Also make a Hₐ.
        --        -- Second projections should use substitutions...
        --        -- Maybe prove strict inversity.
        --        -- **Or prove injectivity & surjectivity.**
        --        (wₐ' + wₜ' , giveArg t' a' )
        --    ≡⟨ ? ⟩
        --        (wₐ + wₜ , giveArg t a) 
        --    ≡∎
        --    where
        --        tNW : OTNW (ℕ.suc n)
        --        tNW = forgetWeight' (wₜ , t) 
        --        aNW : OTNW 0
        --        aNW = forgetWeight' (wₐ , a) 
        --        wₜ' : ℕ
        --        wₜ' = (proj₁ $ addWeight $ forgetWeight' (wₜ , t)) 
        --        t' : OT wₜ' (ℕ.suc n)
        --        t' = (proj₂ $ addWeight $ forgetWeight' (wₜ , t)) 
        --        wₐ' : ℕ
        --        wₐ' = (proj₁ $ addWeight $ forgetWeight' (wₐ , a)) 
        --        a' : OT wₐ' 0
        --        a' = (proj₂ $ addWeight $ forgetWeight' (wₐ , a)) 
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
