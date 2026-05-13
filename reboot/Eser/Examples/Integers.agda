-- Module      : Eser.Examples.Integers
-- Description : Example: constructing type of integers via a quotient.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- This example shows how the type 𝐙 of integers can be constructed by
-- quotienting the inductive type z ::= 0 | S z | P z with a successor- and
-- predecessor-constructor, over the relation (P S z) ~ z ~ (S P z).
-- (i.e., the relation 1 - 1 = 0 = -1 + 1).
--------------------------------------------------------------------------------

open import Level
open import Data.Nat hiding (_/_)
open import Data.Nat.Properties
open import Data.Sum
open import Data.Unit
open import Data.Empty
open import Relation.Binary
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality
open import Relation.Nullary
open import Data.Product
open import Relation.Binary.Structures
open import Function
open import Relation.Binary.Reasoning.Syntax

open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)

open import Eser.Aux using (IsFixpoint ; restIsProofIrrel)
open import Eser.Equivalences.Notation
open import Eser.Equivalences.Properties
open import Eser.EqRel
open import Eser.Quotient.Definitions

module Eser.Examples.Integers where

open import Eser.Examples.Integers.Definitions public
open import Eser.Examples.Integers.DirectEncProperties public
open import Eser.Examples.Integers.NFLeq public
open import Eser.Examples.Integers.NFFix public

--------------------------------------------------------------------------------
-- Proof that ℤ are indeed the integers
--
-- In particular, we show that our quotient type ℤ is equivalent
-- to the definition of integers used in the standard library.
-- The standard library defines integers as the inductive type
-- with constructors:
--      pos      : ℕ → ℤ
--      negsuc   : ℕ → ℤ
-- with the interpretation that:
--      pos n    = + n
--      negsuc n = - (n+1)
-- (This interpretation avoids having distinct +0 and -0.
--------------------------------------------------------------------------------
open import Data.Integer renaming (ℤ to ℤ#) hiding (_/_)
-- ^ _/_ is already imported from Eser.Quotients.Definitions.

nf-fun : NFFun
nf-fun = (nf , nf-leq , nf-fix)

ℤ : Set
ℤ = ℤ'≃ℕ / nf-fun

IsNormal : ℤ' → Set
IsNormal z = IsFixpoint nf (θ z)

-- It holds : (IsClean z) ↔ (nf (ϵ z) ≡ ϵ z)
-- Reason:
-- (1) IsClean z ↔ f z ≡ z
-- (2) nf ≗ elift f ≗ θ ∘ f ∘ θ⁻¹
-- and 
-- (3) elift preserves and reflects fixpoints.
normalIfClean : (z : ℤ') → IsClean z → IsNormal z
normalIfClean z p = 
    ≡begin 
        (θ ∘ f ∘ θ⁻¹ ∘ θ) z
    ≡⟨ cong (θ ∘ f) $ θ⁻¹∘θ≈id z ⟩
        (θ ∘ f) z
    ≡⟨ cong θ $ f-fixes-on-clean-inp z p ⟩
        θ z
    ≡∎

    
cleanIfNormal : (z : ℤ') → IsNormal z → IsClean z
cleanIfNormal z p = z-is-clean
    where
        z-is-fixpoint : f z ≡ z
        z-is-fixpoint = 
                ≡begin 
                    f z
                ≡⟨ cong f $ sym $ θ⁻¹∘θ≈id z ⟩
                    (f ∘ θ⁻¹ ∘ θ ) z
                ≡⟨ sym $ θ⁻¹∘θ≈id $ (f ∘ θ⁻¹ ∘ θ ) z ⟩
                    (θ⁻¹ ∘ θ ∘ f ∘ θ⁻¹ ∘ θ ) z
                ≡⟨ cong θ⁻¹ p ⟩
                    (θ⁻¹ ∘ θ) z
                ≡⟨ θ⁻¹∘θ≈id z ⟩
                    z
                ≡∎
        fz-is-clean : IsClean (f z)
        fz-is-clean = f-cleans z
        z-is-clean : IsClean z
        z-is-clean = subst IsClean z-is-fixpoint fz-is-clean
    

abs : (z : ℤ') → IsClean z → ℕ
abs O     p@(inj₁ isZero)       = 0
abs O     p@(inj₂ (inj₁ ()))
abs O     p@(inj₂ (inj₂ ()))
abs (S z) p@(inj₂ (inj₁ isPos)) = ℕ.suc (abs z $ is-clean-S-downgrade {z} p)
abs (P z) p@(inj₂ (inj₂ isNeg)) = ℕ.suc (abs z $ is-clean-P-downgrade {z} p)

χ : ℤ → ℤ#
χ (z , p) = χcases z $ cleanIfNormal z p
    module χDef where
        k : IsNormal z
        k = p
        χcases : (z : ℤ') → IsClean z → ℤ#
        χcases O     p@(inj₁ isZero) = + (abs O p) 
        χcases O     p@(inj₂ (inj₁ ()))
        χcases O     p@(inj₂ (inj₂ ()))
        χcases (S z) p@(inj₂ (inj₁ isPos)) = +[1+ abs z p' ]
            where
                p' : IsClean z
                p' = is-clean-S-downgrade {z} p
        χcases (P z) p@(inj₂ (inj₂ isNeg)) = -[1+ abs z p' ]
            where
                p' : IsClean z
                p' = is-clean-P-downgrade {z} p
    
-- Make a ℤ' term as a tower of n times `S` applied to O.
S-stack : ℕ → ℤ'
S-stack 0 = O
S-stack (suc n) = S (S-stack n)
P-stack : ℕ → ℤ'
P-stack 0 = O
P-stack (suc n) = P (P-stack n)

S-stack-isPos : (n : ℕ) → IsPos (S-stack $ ℕ.suc n)
S-stack-isPos ℕ.zero = tt
S-stack-isPos (ℕ.suc n) = S-stack-isPos n

P-stack-isNeg : (n : ℕ) → IsNeg (P-stack $ ℕ.suc n)
P-stack-isNeg ℕ.zero = tt
P-stack-isNeg (ℕ.suc n) = P-stack-isNeg n

-- If z is positive then there exist a clean z' s.t. z ≡ S z'.
-- (z' might not be positive, it can also be O).
isPos-to-predec'
    : (z : ℤ')
    → (p : IsPos z)
    → Σ[ z' ∈ ℤ' ] (IsClean z') × (
        Σ[ k ∈ z ≡ S z' ] (
            _≡_ {A = Σ[ z ∈ ℤ' ] IsClean z}
                (z , inj₂ (inj₁ p)) 
                (S z' , (inj₂  (inj₁ $ subst (λ x → IsPos x) k p)))
        )
    )
isPos-to-predec' (S O) tt = (O , inj₁ tt , refl , refl)
isPos-to-predec' (S (S z)) p = 
    (S z 
    , is-clean-S-downgrade {S z} (inj₂ $ inj₁ p)
    , refl
    , refl
    )
-- If z is negative then there exist a clean z' s.t. z ≡ P z'.
-- (z' might not be negative, it can also be O).
isNeg-to-predec
    : (z : ℤ')
    → IsNeg z
    → Σ[ z' ∈ ℤ' ] (z ≡ P z') × IsClean z'
isNeg-to-predec (P O) tt = (O , refl , inj₁ tt)
isNeg-to-predec (P (P z)) p = 
    (P z 
    , refl 
    , is-clean-P-downgrade {P z} (inj₂ $ inj₂ p)
    )


β : ℤ# → ℤ
β +0 = (O , normalIfClean O (inj₁ tt))
β +[1+ n ] = (z , (normalIfClean z $ inj₂ $ inj₁ $ S-stack-isPos n))
    where
        z : ℤ'
        z = S-stack (ℕ.suc n)
β -[1+ n ] = (z , (normalIfClean z $ inj₂ $ inj₂ $ P-stack-isNeg n))
    where
        z : ℤ'
        z = P-stack (ℕ.suc n)
β₀ : ℤ# → ℤ'
β₀ = proj₁ ∘ β
β₁ : (z : ℤ#) → IsNormal (β₀ z)
β₁ = proj₂ ∘ β

isNormalIrrel : (z : ℤ') → Relation.Nullary.Irrelevant (IsNormal z)
isNormalIrrel z = Data.Nat.Properties.≡-irrelevant
isCleanIrrel : (z : ℤ') → Relation.Nullary.Irrelevant (IsClean z)
isCleanIrrel z = ?

is-clean-S-downgrade-nonneg
    : (z : ℤ')
    → (p : IsClean (S z))
    → IsZero z ⊎ IsPos z
is-clean-S-downgrade-nonneg O (inj₂ (inj₁ tt)) = inj₁ tt
is-clean-S-downgrade-nonneg (S z) (inj₂ (inj₁ p)) = inj₂ p
is-clean-S-downgrade-nonneg (P z) (inj₂ (inj₁ ()))
is-clean-S-downgrade-nonneg (P z) (inj₂ (inj₂ ()))

abs-S-stack
    : (n : ℕ) 
    → (p : IsClean (S-stack n))
    → abs (S-stack n) p ≡ n
abs-S-stack ℕ.zero (inj₁ tt) = refl
abs-S-stack ℕ.zero (inj₂ (inj₁ ()))
abs-S-stack ℕ.zero (inj₂ (inj₂ ()))
abs-S-stack (ℕ.suc n) p@(inj₂ (inj₁ isPos)) = 
    ≡begin 
        abs (S-stack (ℕ.suc n)) p
    ≡⟨⟩
        abs (S (S-stack n)) p
    ≡⟨⟩
        ℕ.suc (abs (S-stack n) p')
    ≡⟨ cong ℕ.suc $ abs-S-stack n p' ⟩
        ℕ.suc n
    ≡∎
    where
        p' : IsClean (S-stack n)
        p' = is-clean-S-downgrade {S-stack n} p
S-stack-abs
    : (z : ℤ')
    → (p : IsClean z )
    → (H : IsZero z ⊎ IsPos z)
    → S-stack (abs z p) ≡ z
S-stack-abs O     p@(inj₁ isZero)       _ = refl 
S-stack-abs O     p@(inj₂ (inj₁ ()))
S-stack-abs O     p@(inj₂ (inj₂ ()))
S-stack-abs (S z) p@(inj₂ (inj₁ isPos)) _ =  
    ≡begin 
        S-stack (abs (S z) p)
    ≡⟨⟩
        S-stack (ℕ.suc (abs z p'))
    ≡⟨⟩
        S (S-stack (abs z p'))
    ≡⟨ cong S $ S-stack-abs z p' p'' ⟩
        S z 
    ≡∎
    where
        p' : IsClean z
        p' = is-clean-S-downgrade {z} p
        p'' : IsZero z ⊎ IsPos z
        p'' = is-clean-S-downgrade-nonneg z p

S-stack-abs (P z) p@(inj₂ (inj₂ isNeg)) (inj₁ ())
S-stack-abs (P z) p@(inj₂ (inj₂ isNeg)) (inj₂ ())


clean-tuple-eq
    : (z z' : ℤ')
    → (p : IsClean z)
    → z ≡ z'
    → Σ[ p' ∈ IsClean z' ] ((z , p) ≡ (z' , p'))
clean-tuple-eq z z' p H = (p' , prf)
    where
        p' : IsClean z'
        p' = subst IsClean H p
        prf : (z , p) ≡ (z' , p')
        prf = restIsProofIrrel {A = ℤ'} {B = IsClean} isCleanIrrel {z} {z'} p p' H

ℤcorrectness : ℤ ≃ ℤ#
ℤcorrectness = mk≃' χ β invˡ invʳ
    where
    opaque
        invˡ : Inverseˡ _≡_ _≡_ χ β
        -- Hardest part of proof: the proof of cleanness that χ computes
        -- and passes to χcases is not judgementally equal to (inj₁ tt)
        -- (where tt : IsZero O). But cleanness proofs are irrelevant
        -- and hence we can contract it to this anyway.
        invˡ { +0      } {y} refl = 
            ≡begin 
                χ (β +0)
            ≡⟨⟩
                χ (O , p)
            ≡⟨⟩
                χcases O (cleanIfNormal O p)
            ≡⟨ cong (χcases O) $ isCleanIrrel O (cleanIfNormal O p) (inj₁ tt) ⟩
                χcases O (inj₁ tt)
            ≡⟨⟩
                +0
            ≡∎
            where
                z : ℤ'
                z = β₀ +0
                p : IsNormal O
                p = β₁ +0
                open χDef O p
            
        invˡ { +[1+ n ]} {y} refl =
            ≡begin 
                χ (β +[1+ n ])
            ≡⟨⟩
                χ (z , isNorm)
            ≡⟨⟩
                χcases z (cleanIfNormal z isNorm)
            ≡⟨ cong (χcases z) $ isCleanIrrel z (cleanIfNormal z isNorm) (inj₂ $ inj₁  q) ⟩
                χcases z (inj₂ $ inj₁ q)
            ≡⟨⟩
                uncurry χcases (z , (inj₂ $ inj₁ q))
            ≡⟨ cong (uncurry χcases) $ proj₂ $ proj₂ $ proj₂ $ isPos-to-predec' z q  ⟩
                uncurry χcases (S z' , (inj₂ $ inj₁ q'))
            ≡⟨⟩
                χcases (S z') (inj₂ $ inj₁ q')
            ≡⟨⟩
                +[1+ abs z' p' ] 
            ≡⟨⟩
                +[1+_] (uncurry abs (z' , p'))
            ≡⟨ cong (λ x → +[1+_] (uncurry abs x)) 
                $ proj₂ $ clean-tuple-eq z' (S-stack n) p' K  ⟩
                +[1+_] (uncurry abs (S-stack n , p''))
            ≡⟨⟩
                +[1+_] (abs (S-stack n ) p'')
            ≡⟨ cong +[1+_] $ abs-S-stack n p'' ⟩
                +[1+ n ]
            ≡∎
            where
                z : ℤ'
                z = S-stack (ℕ.suc n)
                isNorm : IsNormal z
                isNorm = normalIfClean z $ inj₂ $ inj₁ $ S-stack-isPos n
                open χDef z isNorm
                q : IsPos z
                q = S-stack-isPos n
                p : IsClean z
                p = inj₂ $ inj₁ $ q
                z' : ℤ'
                z' = proj₁ $ isPos-to-predec' z q
                z≡Sz' : z ≡ S z'
                z≡Sz' = proj₁ $ proj₂ $ proj₂ $ isPos-to-predec' z q
                q' : IsPos (S z')
                q' = subst (λ x → IsPos x) z≡Sz' q
                p' : IsClean z'
                p' = is-clean-S-downgrade {z'} (inj₂ $ inj₁ $ q')
                K : z' ≡ S-stack n
                K = S-injective z' (S-stack n) (sym z≡Sz')
                p'' : IsClean (S-stack n)
                p'' = proj₁ $ clean-tuple-eq z' (S-stack n) p' K

        invˡ { -[1+ n ]} {y} refl = {! !} -- Symmetric to case above!
        invʳ : Inverseʳ _≡_ _≡_ χ β
        invʳ {z , isNorm} {x} refl = 
            sym $ restIsProofIrrel {A = ℤ'} 
                {B = IsNormal} 
                isNormalIrrel 
                {z} 
                {z'}
                isNorm 
                isNorm' 
                (sym $ χcases-invʳ z p)
            where
                open χDef z isNorm
                p : IsClean z
                p = cleanIfNormal z isNorm
                z' : ℤ'
                z' =  β₀ (χcases z p)
                isNorm' : IsNormal z'
                isNorm' = β₁ $ χcases z p
                -- Make case distinction; this will make things compute,
                -- since χ is defined as the
                -- case distinction `χcases`.
                --    → β (χcases z p) ≡ (z , isNorm)
                χcases-invʳ 
                    : (z : ℤ') 
                    → (p : IsClean z) 
                    → β₀ (χcases z p) ≡ z
                χcases-invʳ O (inj₁ tt) = refl
                χcases-invʳ O (inj₂ (inj₁ ()))
                χcases-invʳ O (inj₂ (inj₂ ()))
                χcases-invʳ (S z) p@(inj₂ (inj₁ isPos)) = 
                    ≡begin 
                        β₀ (χcases (S z) (inj₂ (inj₁ isPos))) 
                    ≡⟨⟩
                        β₀ +[1+ abs z p' ]
                    ≡⟨⟩
                        S-stack (ℕ.suc (abs z p'))
                    ≡⟨⟩
                        S (S-stack (abs z p'))
                    ≡⟨ cong S $ S-stack-abs z p' p'' ⟩
                        S z
                    ≡∎
                    where
                        p' : IsClean z
                        p' = is-clean-S-downgrade {z} p
                        p'' : IsZero z ⊎ IsPos z
                        p'' = is-clean-S-downgrade-nonneg z p
                    
                χcases-invʳ (P z) (inj₂ (inj₂ isNeg)) = {! !} -- Symmetric to previoous



_ℤ+_ : ℤ → ℤ → ℤ
_ℤ+_ = ?
