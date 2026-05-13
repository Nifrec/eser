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
            ≡⟨ cong (χcases z) 
                $ isCleanIrrel z (cleanIfNormal z isNorm) (inj₂ $ inj₁  q) ⟩
                χcases z (inj₂ $ inj₁ q)
            ≡⟨⟩
                uncurry χcases (z , (inj₂ $ inj₁ q))
            ≡⟨ cong (uncurry χcases) 
                $ proj₂ $ proj₂ $ proj₂ $ isPos-to-predec' z q  ⟩
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

        -- This case is symmetric to the case above, only with exchanged:
        -- S ↔ P
        -- Pos ↔ Neg
        -- and some (inj₂ ∘ inj₁) replaced by (inj₂ ∘ inj₂) (in proofs of
        -- IsClean, since IsNeg is the third injection and IsPos the second).
        -- Otherwise it is just a copy-paste. 
        -- I didn't see a way to avoid the duplication.
        invˡ { -[1+ n ]} {y} refl = 
            ≡begin 
                χ (β -[1+ n ])
            ≡⟨⟩
                χ (z , isNorm)
            ≡⟨⟩
                χcases z (cleanIfNormal z isNorm)
            ≡⟨ cong (χcases z) $ isCleanIrrel z (cleanIfNormal z isNorm) (inj₂ $ inj₂  q) ⟩
                χcases z (inj₂ $ inj₂ q)
            ≡⟨⟩
                uncurry χcases (z , (inj₂ $ inj₂ q))
            ≡⟨ cong (uncurry χcases) $ proj₂ $ proj₂ $ proj₂ $ isNeg-to-predec' z q  ⟩
                uncurry χcases (P z' , (inj₂ $ inj₂ q'))
            ≡⟨⟩
                χcases (P z') (inj₂ $ inj₂ q')
            ≡⟨⟩
                -[1+ abs z' p' ] 
            ≡⟨⟩
                -[1+_] (uncurry abs (z' , p'))
            ≡⟨ cong (λ x → -[1+_] (uncurry abs x)) 
                $ proj₂ $ clean-tuple-eq z' (P-stack n) p' K  ⟩
                -[1+_] (uncurry abs (P-stack n , p''))
            ≡⟨⟩
                -[1+_] (abs (P-stack n ) p'')
            ≡⟨ cong -[1+_] $ abs-P-stack n p'' ⟩
                -[1+ n ]
            ≡∎
            where
                z : ℤ'
                z = P-stack (ℕ.suc n)
                isNorm : IsNormal z
                isNorm = normalIfClean z $ inj₂ $ inj₂ $ P-stack-isNeg n
                open χDef z isNorm
                q : IsNeg z
                q = P-stack-isNeg n
                p : IsClean z
                p = inj₂ $ inj₂ $ q
                z' : ℤ'
                z' = proj₁ $ isNeg-to-predec' z q
                z≡Pz' : z ≡ P z'
                z≡Pz' = proj₁ $ proj₂ $ proj₂ $ isNeg-to-predec' z q
                q' : IsNeg (P z')
                q' = subst (λ x → IsNeg x) z≡Pz' q
                p' : IsClean z'
                p' = is-clean-P-downgrade {z'} (inj₂ $ inj₂ $ q')
                K : z' ≡ P-stack n
                K = P-injective z' (P-stack n) (sym z≡Pz')
                p'' : IsClean (P-stack n)
                p'' = proj₁ $ clean-tuple-eq z' (P-stack n) p' K


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
                    
                -- Symmetric to previous case, litterally copy-pasted,
                -- as in the invˡ proof.
                χcases-invʳ (P z) p@(inj₂ (inj₂ isNeg)) = 
                    ≡begin 
                        β₀ (χcases (P z) (inj₂ (inj₂ isNeg))) 
                    ≡⟨⟩
                        β₀ -[1+ abs z p' ]
                    ≡⟨⟩
                        P-stack (ℕ.suc (abs z p'))
                    ≡⟨⟩
                        P (P-stack (abs z p'))
                    ≡⟨ cong P $ P-stack-abs z p' p'' ⟩
                        P z
                    ≡∎
                    where
                        p' : IsClean z
                        p' = is-clean-P-downgrade {z} p
                        p'' : IsZero z ⊎ IsNeg z
                        p'' = is-clean-P-downgrade-nonpos z p


_ℤ+_ : ℤ → ℤ → ℤ
_ℤ+_ = ?
