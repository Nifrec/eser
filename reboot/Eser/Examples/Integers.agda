-- Module      : Eser.Integers
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
--
-- Implementation note: we define the terms of
-- z ::= 0 | S z | P z
-- both via the `data` keyword (as ℤ')
-- and as the closed terms (as 𝕋) over a signature ℤSig.
-- In principle, we could do all the proofs and correspondences without
-- using the `data` keyword, but this gets thorny because Agda cannot do proper
-- pattern-matching on the elements of ℤ' because it fails to unify 
-- the wₐ + wₜ index in the output of giveArg.
-- This can probably be circumvented by proving that 
-- termCharacterisation
--  : {w : ℕ} 
--  → (t : ClosedTerms ℤSig w) 
--  → (t ≡ O) 
--      ⊎ Σ[ a ∈ ℤ' ] (t ≡ S (proj₂ a))
--      ⊎ Σ[ a ∈ ℤ' ] (t ≡ P (proj₂ a))
-- where:
-- O : ℤ'
-- O = (1 , mk-nullary Fin.zero)

-- S : {w : ℕ} → ClosedTerms {fin 1} {fin 2} ℤSig w → ℤ'
-- S {w} a = (w + 1 , giveArg (mk-multiary Fin.zero) a)

-- P : {w : ℕ} → ClosedTerms {fin 1} {fin 2} ℤSig w → ℤ'
-- P {w} a = (w + 2 , giveArg (mk-multiary $ Fin.suc Fin.zero) a)
--
-- But this approach is less readable and more work
-- than defining the raw terms just via the `data` keyword.

open import Level
open import Data.Bool hiding (_≤_ ; _<_ ; _≤?_)
open import Data.Bool.Properties
open import Data.Nat hiding (_/_)
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
open import Eser.Equivalences.Notation
open import Eser.Equivalences.Properties
open import Eser.Aux
open import Eser.Signature
open import Eser.EqRel
open import Eser.Quotient.Definitions

module Eser.Examples.Integers where

-- Terms of the grammar z ::= 0 | S z | P z.
data ℤ' : Set where
    O : ℤ'
    S : ℤ' → ℤ'
    P : ℤ' → ℤ'

-- Signature representing the inductive type z ::= 0 | S z | P z.
-- One nullary constructor: 0
-- Two 1-ary constructors: S and P
ℤSig : Signature (fin 1) (fin 2)
ℤSig (Fin.zero) = 0                 -- The arity - 1 of S is 0.
ℤSig (Fin.suc Fin.zero) = 0         -- The arity - 1 of P is 0.

-- Set of all closed terms over ℤSig.
-- It still has different elements, 
-- for example, for `P S 0`, `S P 0` and `0`.
𝕋 : Set
𝕋 = AllTerms {fin 1} {fin 2} ℤSig
--
-- ℤ' is equivalent to the set of all closed terms over ℤSig.
ℤ'≃𝕋 : ℤ' ≃ 𝕋
ℤ'≃𝕋 = ?

ℤenum : ℤ' ≃ ℕ
ℤenum = ≃-trans ℤ'≃𝕋 (infTermAlgEnum {fin 0} {fin 1} ℤSig)

open ForEnumSet ℤenum

nf' : ℤ' → ℤ'
nf' O = O
nf' (S O) = S O
nf' (P O) = P O
nf' (S (P t)) = nf' t
nf' (P (S t)) = nf' t
nf' (S (S t)) = S $ S $ nf' t
nf' (P (P t)) = P $ P $ nf' t

nf : ℕ → ℕ
nf = φ ∘ nf' ∘ φ⁻¹ 

--------------------------------------------------------------------------------
-- #TODO: probably remove/rename/retype stuff in this section.
--------------------------------------------------------------------------------

-- Proofs that `nf` satisfies the properties of a normal-form function.
nf-leq : NFLeq nf
nf-leq = ?

nf-fix : NFFix nf
nf-fix = ?

-- Actual integers: quotient of ℤ' by the relation encoded in nf.
ℤ : Set
ℤ = ℤenum / (nf , nf-leq , nf-fix)

--------------------------------------------------------------------------------
-- NF without inductive type
--------------------------------------------------------------------------------
module DEPRECATED where
    C : ℕ → Set
    C = ClosedTerms {fin 1} {fin 2} ℤSig

    𝟎 : 𝕋
    𝟎 = (1 , mk-nullary Fin.zero)

    𝐒 : {w : ℕ} → C w → 𝕋
    𝐒 {w} a = (w + 1 , giveArg (mk-multiary Fin.zero) a)

    𝐏 : {w : ℕ} → C w → 𝕋
    𝐏 {w} a = (w + 2 , giveArg (mk-multiary $ Fin.suc Fin.zero) a)


    --𝟎 : C 1
    --𝟎 = mk-nullary Fin.zero

    --𝐒 : {w : ℕ} → C w → C (w + 1)
    --𝐒 = giveArg (mk-multiary Fin.zero)

    --𝐏 : {w : ℕ} → C w → C (w + 2)
    --𝐏 = giveArg (mk-multiary $ Fin.suc Fin.zero)

    ---- Pattern-matching lemma. We can simulate ℤ' pattern matching.
    ---- Just a whole lot more cumbersome.
    --pama-lemma
    --    : {w : ℕ} 
    --    → (t : ClosedTerms {fin 1} {fin 2} ℤSig w)
    --    → t ≡ 𝟎 ⊎ Σ[ a ∈ ℤ' ] ((w , t) ≡ S (proj₂ a)) ⊎ Σ[ a ∈ ℤ' ] ((w , t) ≡ P (proj₂ a))

    -- Pattern-matching lemma. We can simulate ℤ' pattern matching.
    -- Just a whole lot more cumbersome.
    pama-lemma
        : (t : 𝕋) -- ClosedTerms {fin 1} {fin 2} ℤSig w)
        → t ≡ 𝟎 ⊎ Σ[ a ∈ 𝕋 ] (t ≡ 𝐒 (proj₂ a)) ⊎ Σ[ a ∈ 𝕋 ] (t ≡ 𝐏 (proj₂ a))
    pama-lemma (fst , mk-nullary Fin.zero) = {! !}
    pama-lemma (fst , giveArg snd snd₁) = {! !}

--------------------------------------------------------------------------------
-- NF without inductive type without weights
--------------------------------------------------------------------------------
module NoWeights where

    private
        C : Set
        C = ClosedTermsNW {fin 1} {fin 2} ℤSig

        OT : ℕ → Set
        OT = OpenTermsNW {fin 1} {fin 2} ℤSig

    𝟎 : C
    𝟎 = mk-nullary-nw Fin.zero

    𝐒 : C → C
    𝐒 = giveArg-nw $ mk-multiary-nw Fin.zero

    𝐏 : C → C
    𝐏 = giveArg-nw $ mk-multiary-nw $ Fin.suc Fin.zero

    pama-strictly-open
        : (t : OT 1)
        → (t ≡ mk-multiary-nw Fin.zero)
          ⊎ 
          (t ≡ mk-multiary-nw (Fin.suc Fin.zero))
    pama-strictly-open t = ?
        where
            -- Help Agda with inferring underlying base type.
            _≡ₒₜ_ : Rel (Σ[ n ∈ ℕ ] (OT n)) 0ℓ
            x ≡ₒₜ y = _≡_ {A = Σ[ n ∈ ℕ ] (OT n)} x y
            -- Abstract n as a variable, to be able to do pattern-matching.
            sublemma
                : {n : ℕ}
                → (t : OT n)
                → n ≡ 1
                → ((n , t) ≡ₒₜ (1 , mk-multiary-nw Fin.zero))
                  ⊎ 
                  ((n , t) ≡ₒₜ (1 , mk-multiary-nw (Fin.suc Fin.zero)))
            sublemma {n} (mk-multiary-nw Fin.zero) H = {! !}
            sublemma {n} (mk-multiary-nw (Fin.suc c)) H = {! !}
            sublemma {n} (giveArg-nw t a) H = {! !}


    -- Pattern-matching lemma. We can simulate ℤ' pattern matching.
    -- Just a whole lot more cumbersome.
    pama-lemma
        : (t : C)
        → t ≡ 𝟎 ⊎ Σ[ a ∈ C ] (t ≡ 𝐒 a) ⊎ Σ[ a ∈ C ] (t ≡ 𝐏 a)
    pama-lemma (mk-nullary-nw Fin.zero) = inj₁ refl
    pama-lemma (giveArg-nw t a) with pama-strictly-open t
    ... | inj₁ t≡𝐒 = inj₂ $ inj₁ $ (a , cong (λ t → giveArg-nw t a) t≡𝐒)
    ... | inj₂ t≡𝐏 = inj₂ $ inj₂ $ (a , cong (λ t → giveArg-nw t a) t≡𝐏)

    -- Normalisation function defined on terms of ℤSig.
    -- It essentially implements nf' above, but acts on the representation
    -- of terms of ℤSig instead of ℤ'.
    f : C → C
    f t = f' t $ pama-lemma t
        where
            -- Nested case distinction on the form of t.
            -- See below for the annotated cases.
            fₛ  : (t a : C) 
                → (t ≡ 𝐒 a)
                → a ≡ 𝟎 ⊎ Σ[ a' ∈ C ] (a ≡ 𝐒 a') ⊎ Σ[ a' ∈ C ] (a ≡ 𝐏 a')
                → C
            fₚ  : (t a : C) 
                → (t ≡ 𝐏 a)
                → a ≡ 𝟎 ⊎ Σ[ a' ∈ C ] (a ≡ 𝐒 a') ⊎ Σ[ a' ∈ C ] (a ≡ 𝐏 a')
                → C

            f'  : (t : C) 
                → t ≡ 𝟎 ⊎ Σ[ a ∈ C ] (t ≡ 𝐒 a) ⊎ Σ[ a ∈ C ] (t ≡ 𝐏 a)
                → C
            f' t (inj₁ t≡𝟎) = 𝟎
            f' t (inj₂ (inj₁ (a , t≡𝐒a))) = fₛ t a t≡𝐒a (pama-lemma a)
            f' t (inj₂ (inj₂ (a , t≡𝐏a))) = fₚ t a t≡𝐏a (pama-lemma a)

            -- Case 1 : t ≡ 𝐒 𝟎, which is already normal.
            fₛ t a refl (inj₁ a≡𝟎) = 𝐒 𝟎 
            -- Case 2 : t ≡ 𝐒 𝐒 a'; return 𝐒 𝐒 (f a')
            fₛ t a refl (inj₂ (inj₁  (a' , a≡𝐒a'))) = 𝐒 ( 𝐒 ( f a'))
            -- Case 3 : t ≡ 𝐒 𝐏 a'; inversity applies, so return (f a')
            fₛ t a refl (inj₂ ( inj₂ (a' , a≡𝐏a'))) = f a'
            -- Case 4 : t ≡ 𝐏 𝟎, which is already normal.
            fₚ t a refl (inj₁ a≡𝟎) = 𝐏 𝟎 
            -- Case 5 : t ≡ 𝐏 𝐒 a'; inversity applies, so return f a'
            fₚ t a refl (inj₂ (inj₁  (a' , a≡𝐒a'))) = f a'
            -- Case 6 : t ≡ 𝐏 𝐏 a'; return (f a')
            fₚ t a refl (inj₂ ( inj₂ (a' , a≡𝐏a'))) = 𝐏 (𝐏 (f a'))

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
import Data.Integer
module StdlibInt = Data.Integer

ℤcorrectness : ℤ ≃ StdlibInt.ℤ
ℤcorrectness = ?
