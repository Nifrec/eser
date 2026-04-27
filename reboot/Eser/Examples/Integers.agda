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


--------------------------------------------------------------------------------
-- NF without inductive type
--------------------------------------------------------------------------------
module DEPRECATED where
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
    nf' (S (S t)) = S $ nf' $ S t
    nf' (P (P t)) = P $ nf' $ P t

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
-- TODO: move this to another file
--
-- Tools for lifting (properties of) function on A to functions on ℕ.
--------------------------------------------------------------------------------
module EnumLifts {A : Set} (A≃ℕ : A ≃ ℕ) where
    open ForEnumSet A≃ℕ

    elift : (A → A) → ℕ → ℕ
    elift f = φ ∘ f ∘ φ⁻¹

    elift-leq
        : (f : A → A)
        → ((a : A) → f a «= a)
        → ((n : ℕ) → (elift f) n ≤ n)
    elift-leq = ?

    elift-fix
        : (f : A → A)
        → ((a : A) → f (f a) ≡ f a)
        -- → ((n : ℕ) → (elift f $ elift f $ n) ≡ (elift f $ n))
        → ((n : ℕ) → (elift f ( elift f n)) ≡ (elift f n))
    elift-fix = ?



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

    --syntax 𝟎' = 𝟎

    𝐒 : C → C
    𝐒 t = giveArg-nw ( mk-multiary-nw Fin.zero ) t

    𝐏' : C → C
    𝐏' = giveArg-nw $ mk-multiary-nw $ Fin.suc Fin.zero

    syntax 𝐏' t = 𝐏 t

    C≃ℕ : C ≃ ℕ
    C≃ℕ = infTermAlgEnumNW {fin 0} {fin 1} ℤSig

    open ForEnumSet C≃ℕ

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
            sublemma {n} (giveArg-nw t a) H = {! !} -- #TODO: derive contradiction

    --wₛ : {n : ℕ} → OT n → OT n
    --wₚ : {n : ℕ} → OT n → OT n

    meh : {n : ℕ} → (t t' : OT n) → Relation.Nullary.Dec (t ≡ t')
    meh = ?

    w : OT 0 → OT 0
    w' : OT 1 → OT 0 → OT 0
    w t@(mk-nullary-nw c) = t
    w (giveArg-nw t' a) = w' t' a
    w' t' a@(mk-nullary-nw c) = giveArg-nw t' a
    w' t' a@(giveArg-nw t'' a') with meh t' t''
    ... | yes refl = giveArg-nw t' $ w' t'' a'
    ... | no  t'≢t'' = w a'


    --wₛ : {n : ℕ} → OT n → OT n
    --wₚ : {n : ℕ} → OT n → OT n
    --w : {n : ℕ} → OT n → OT n
    --w {n} t@(mk-nullary-nw c) = t 
    --w {n} t@(mk-multiary-nw c) = t 
    --w {n} t@(giveArg-nw t' (mk-nullary-nw c)) = t
    --w {ℕ.zero} t@(giveArg-nw t' (giveArg-nw a a')) = w $ giveArg-nw a a'
    ---- Case below: t' must have at least 2 holes.
    --w {ℕ.suc n} t@(giveArg-nw t' (giveArg-nw a a')) = t -- wrong, need ⊥-elim

    --qₛ : C → C
    --qₜ : C → C
    --q : C → C
    --q t@(mk-nullary-nw Fin.zero) = t
    --q (giveArg-nw t a) = {! !}



    --q (mk-nullary-nw Fin.zero) = {! !}
    ---- #TODO: case distinction on t before on a.
    --q (giveArg-nw t a) with pama-strictly-open t
    --q t@(giveArg-nw t' (mk-nullary-nw Fin.zero)) | inj₁ refl = t
    --q (giveArg-nw t (giveArg-nw a a')) | inj₁ refl with pama-strictly-open a
    ---- Case t ≡ 𝐒 𝐒 a'
    --... | inj₁ refl = 𝐒 $ q $ giveArg-nw (mk-multiary-nw (Fin.zero)) a'
    ---- Case t ≡ 𝐒 𝐏 a'
    --... | inj₂ refl = q a'
    --q t@(giveArg-nw t' (mk-nullary-nw Fin.zero)) | inj₂ refl = t
    --q (giveArg-nw t (giveArg-nw a a')) | inj₂ refl = {! !}

    -- Pattern-matching lemma. We can simulate ℤ' pattern matching.
    -- Just a whole lot more cumbersome.
    pama-lemma
        : (t : C)
        → t ≡ 𝟎 ⊎ Σ[ a ∈ C ] (t ≡ 𝐒 a) ⊎ Σ[ a ∈ C ] (t ≡ 𝐏 a)
    pama-lemma (mk-nullary-nw Fin.zero) = inj₁ refl
    pama-lemma (giveArg-nw t a) with pama-strictly-open t
    ... | inj₁ t≡𝐒 = inj₂ $ inj₁ $ (a , cong (λ t → giveArg-nw t a) t≡𝐒)
    ... | inj₂ t≡𝐏 = inj₂ $ inj₂ $ (a , cong (λ t → giveArg-nw t a) t≡𝐏)

    SinglePaMaCases : (t : C) → Set
    SinglePaMaCases t = t ≡ 𝟎 ⊎ Σ[ a ∈ C ] (t ≡ 𝐒 a) ⊎ Σ[ a ∈ C ] (t ≡ 𝐏 a)

    PaMaCases : (t : C) → Set
    PaMaCases t = t ≡ 𝟎 
                  ⊎ 
                  t ≡ 𝐒 𝟎 
                  ⊎ 
                  t ≡ 𝐏 𝟎 
                  ⊎ 
                  Σ[ a ∈ C ] (t ≡ 𝐒 (𝐒 a)) 
                  ⊎
                  Σ[ a ∈ C ] (t ≡ 𝐒 (𝐏 a)) 
                  ⊎ 
                  Σ[ a ∈ C ] (t ≡ 𝐏 (𝐒 a))
                  ⊎ 
                  Σ[ a ∈ C ] (t ≡ 𝐏 (𝐏 a))
    case1 : {t : C} → t ≡ 𝟎 → PaMaCases t
    case1 = inj₁
    case2 : {t : C} → t ≡ 𝐒 𝟎 → PaMaCases t
    case2 = inj₂ ∘ inj₁
    case3 : {t : C} → t ≡ 𝐏 𝟎 → PaMaCases t
    case3 = inj₂ ∘ inj₂ ∘ inj₁
    case4 : {t : C} → Σ[ a ∈ C ] (t ≡ 𝐒 (𝐒 a)) → PaMaCases t
    case4 = inj₂ ∘ inj₂ ∘ inj₂ ∘ inj₁
    case5 : {t : C} → Σ[ a ∈ C ] (t ≡ 𝐒 (𝐏 a)) → PaMaCases t
    case5 = inj₂ ∘ inj₂ ∘ inj₂ ∘ inj₂ ∘ inj₁
    case6 : {t : C} → Σ[ a ∈ C ] (t ≡ 𝐏 (𝐒 a)) → PaMaCases t
    case6 = inj₂ ∘ inj₂ ∘ inj₂ ∘ inj₂ ∘ inj₂ ∘ inj₁
    case7 : {t : C} → Σ[ a ∈ C ] (t ≡ 𝐏 (𝐏 a)) → PaMaCases t
    case7 = inj₂ ∘ inj₂ ∘ inj₂ ∘ inj₂ ∘ inj₂ ∘ inj₂ 
    --^ Fun fact: case7 is the only one ending in inj₂

    syntax case7 x = inj7 x

    -- Iterating the pama-lemma gives 7 cases
    double-pama-lemma : (t : C) → PaMaCases t
    double-pama-lemma t = sublemma t (pama-lemma t)
        where
            sublemma 
                : (t : C) 
                → t ≡ 𝟎 ⊎ Σ[ a ∈ C ] (t ≡ 𝐒 a) ⊎ Σ[ a ∈ C ] (t ≡ 𝐏 a)
                → PaMaCases t
            sublemmaₛ
                : (t a : C) 
                → t ≡ 𝐒 a
                → a ≡ 𝟎 ⊎ Σ[ a' ∈ C ] (a ≡ 𝐒 a') ⊎ Σ[ a' ∈ C ] (a ≡ 𝐏 a')
                → PaMaCases t
            sublemmaₚ
                : (t a : C) 
                → t ≡ 𝐏 a
                → a ≡ 𝟎 ⊎ Σ[ a' ∈ C ] (a ≡ 𝐒 a') ⊎ Σ[ a' ∈ C ] (a ≡ 𝐏 a')
                → PaMaCases t
            sublemma t (inj₁ refl) = case1 refl
            sublemma t (inj₂ (inj₁ (a , refl))) = sublemmaₛ t a refl (pama-lemma a)
            sublemma t (inj₂ (inj₂ (a , refl))) = sublemmaₚ t a refl (pama-lemma a)
          
            sublemmaₛ t a refl (inj₁ refl) = case2 refl
            sublemmaₛ t a refl (inj₂ (inj₁ (a' , refl))) = case4 (a' , refl)
            sublemmaₛ t a refl (inj₂ (inj₂ (a' , refl))) = case5 (a' , refl)
          
            sublemmaₚ t a refl (inj₁ refl) = case3 refl
            sublemmaₚ t a refl (inj₂ (inj₁ (a' , refl))) = case6 (a' , refl)
            sublemmaₚ t a refl (inj₂ (inj₂ (a' , refl))) = case7 (a' , refl)
          
    --double-pama-lemma (mk-nullary-nw Fin.zero) = inj₁ refl
    --double-pama-lemma (giveArg-nw t a) with pama-strictly-open t

    -- Normalisation function defined on terms of ℤSig.
    -- It essentially implements nf' above, but acts on the representation
    -- of terms of ℤSig instead of ℤ'.
    private 
        Codom : C → Set
        Codom t = Σ[ t' ∈ C ] (t' «= t)

    f : (t : C) → Σ[ t' ∈ C ] (t' «= t)
    f t = «-rec {Codom} F t
        module C-NF where 
            F : ( (t : C) → ((t' : C) → (t' « t) → Codom t') → Codom t)
            f'  : (t : C) 
                → ((t' : C) → (t' « t) → Codom t')
                → t ≡ 𝟎 ⊎ Σ[ a ∈ C ] (t ≡ 𝐒 a) ⊎ Σ[ a ∈ C ] (t ≡ 𝐏 a)
                → Codom t
            F t rec = f' t rec (pama-lemma t)

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

            f' t rec (inj₁ t≡𝟎) = (𝟎 , ?)
            f' t rec (inj₂ (inj₁ (a , t≡𝐒a))) = fₛ t a t≡𝐒a (pama-lemma a) , ?
            f' t rec (inj₂ (inj₂ (a , t≡𝐏a))) = fₚ t a t≡𝐏a (pama-lemma a) , ?

            -- Case 1 : t ≡ 𝐒 𝟎, which is already normal.
            fₛ t a refl (inj₁ a≡𝟎) = 𝐒 𝟎 
            -- Case 2 : t ≡ 𝐒 𝐒 a'; return 𝐒 𝐒 (f a')
            fₛ t a refl (inj₂ (inj₁  (a' , a≡𝐒a'))) = 𝐒 ( 𝐒 ( {! f a' !}))
            -- Case 3 : t ≡ 𝐒 𝐏 a'; inversity applies, so return (f a')
            fₛ t a refl (inj₂ ( inj₂ (a' , a≡𝐏a'))) = {! f a' !}
            -- Case 4 : t ≡ 𝐏 𝟎, which is already normal.
            fₚ t a refl (inj₁ a≡𝟎) = 𝐏 𝟎 
            -- Case 5 : t ≡ 𝐏 𝐒 a'; inversity applies, so return f a'
            fₚ t a refl (inj₂ (inj₁  (a' , a≡𝐒a'))) = {! f a' !}
            -- Case 6 : t ≡ 𝐏 𝐏 a'; return (f a')
            fₚ t a refl (inj₂ ( inj₂ (a' , a≡𝐏a'))) = 𝐏 (𝐏 ({! f a' !}))

    ---- Normalisation function defined on terms of ℤSig.
    ---- It essentially implements nf' above, but acts on the representation
    ---- of terms of ℤSig instead of ℤ'.
    --f : C → C
    --f t = f' t $ pama-lemma t
    --    where
    --        -- Nested case distinction on the form of t.
    --        -- See below for the annotated cases.
    --        fₛ  : (t a : C) 
    --            → (t ≡ 𝐒 a)
    --            → a ≡ 𝟎 ⊎ Σ[ a' ∈ C ] (a ≡ 𝐒 a') ⊎ Σ[ a' ∈ C ] (a ≡ 𝐏 a')
    --            → C
    --        fₚ  : (t a : C) 
    --            → (t ≡ 𝐏 a)
    --            → a ≡ 𝟎 ⊎ Σ[ a' ∈ C ] (a ≡ 𝐒 a') ⊎ Σ[ a' ∈ C ] (a ≡ 𝐏 a')
    --            → C

    --        f'  : (t : C) 
    --            → t ≡ 𝟎 ⊎ Σ[ a ∈ C ] (t ≡ 𝐒 a) ⊎ Σ[ a ∈ C ] (t ≡ 𝐏 a)
    --            → C
    --        f' t (inj₁ t≡𝟎) = 𝟎
    --        f' t (inj₂ (inj₁ (a , t≡𝐒a))) = fₛ t a t≡𝐒a (pama-lemma a)
    --        f' t (inj₂ (inj₂ (a , t≡𝐏a))) = fₚ t a t≡𝐏a (pama-lemma a)

    --        -- Case 1 : t ≡ 𝐒 𝟎, which is already normal.
    --        fₛ t a refl (inj₁ a≡𝟎) = 𝐒 𝟎 
    --        -- Case 2 : t ≡ 𝐒 𝐒 a'; return 𝐒 𝐒 (f a')
    --        fₛ t a refl (inj₂ (inj₁  (a' , a≡𝐒a'))) = 𝐒 ( 𝐒 ( f a'))
    --        -- Case 3 : t ≡ 𝐒 𝐏 a'; inversity applies, so return (f a')
    --        fₛ t a refl (inj₂ ( inj₂ (a' , a≡𝐏a'))) = f a'
    --        -- Case 4 : t ≡ 𝐏 𝟎, which is already normal.
    --        fₚ t a refl (inj₁ a≡𝟎) = 𝐏 𝟎 
    --        -- Case 5 : t ≡ 𝐏 𝐒 a'; inversity applies, so return f a'
    --        fₚ t a refl (inj₂ (inj₁  (a' , a≡𝐒a'))) = f a'
    --        -- Case 6 : t ≡ 𝐏 𝐏 a'; return (f a')
    --        fₚ t a refl (inj₂ ( inj₂ (a' , a≡𝐏a'))) = 𝐏 (𝐏 (f a'))

    ---- Normalisation function defined on terms of ℤSig.
    ---- It essentially implements nf' above, but acts on the representation
    ---- of terms of ℤSig instead of ℤ'.
    --g : C → C
    --g t = g' t $ pama-lemma t
    --    where
    --        -- Nested case distinction on the form of t.
    --        -- See below for the annotated cases.
    --        gₛ  : (t a : C) 
    --            → (t ≡ 𝐒 a)
    --            → a ≡ 𝟎 ⊎ Σ[ a' ∈ C ] (a ≡ 𝐒 a') ⊎ Σ[ a' ∈ C ] (a ≡ 𝐏 a')
    --            → C
    --        gₚ  : (t a : C) 
    --            → (t ≡ 𝐏 a)
    --            → a ≡ 𝟎 ⊎ Σ[ a' ∈ C ] (a ≡ 𝐒 a') ⊎ Σ[ a' ∈ C ] (a ≡ 𝐏 a')
    --            → C

    --        g'  : (t : C) 
    --            → t ≡ 𝟎 ⊎ Σ[ a ∈ C ] (t ≡ 𝐒 a) ⊎ Σ[ a ∈ C ] (t ≡ 𝐏 a)
    --            → C

    --        g' t (inj₁ refl) = 𝟎
    --        g' t (inj₂ (inj₁ (a , refl))) = gₛ t a refl (pama-lemma a)
    --        g' t (inj₂ (inj₂ (a , refl))) = gₚ t a refl (pama-lemma a)

    --        -- Case 1 : t ≡ 𝐒 𝟎, which is already normal.
    --        gₛ t 𝟎 refl (inj₁ refl) = 𝐒 𝟎 
    --        -- Case 2 : t ≡ 𝐒 𝐒 a'; return 𝐒 𝐒 (g a')
    --        gₛ t (giveArg-nw (mk-multiary-nw Fin.zero) a') refl (inj₂ (inj₁  (a' , refl))) = 𝐒 ( g (𝐒 a'))
    --        -- Case 3 : t ≡ 𝐒 𝐏 a'; inversity applies, so return (g a')
    --        gₛ t a refl (inj₂ ( inj₂ (a' , refl))) = g a'
    --        -- Case 4 : t ≡ 𝐏 𝟎, which is already normal.
    --        gₚ t a refl (inj₁ refl) = 𝐏 𝟎 
    --        -- Case 5 : t ≡ 𝐏 𝐒 a'; inversity applies, so return g a'
    --        gₚ t a refl (inj₂ (inj₁  (a' , refl))) = g a'
    --        -- Case 6 : t ≡ 𝐏 𝐏 a'; return (g a')
    --        gₚ t a refl (inj₂ ( inj₂ (a' , refl))) = 𝐏 ( g a)

    --h'' : (t : C) → PaMaCases t → C
    ---- Case 1 : t ≡ 𝟎
    --h'' t (inj₁ refl) = t
    ---- Case 2 : t ≡ 𝐒 𝟎, which is already normal.
    --h'' t (inj₂ (inj₁ refl)) = t
    ---- Case 3 : t ≡ 𝐏 𝟎, which is already normal.
    --h'' t (inj₂ ( inj₂ ( inj₁ refl))) = t
    ---- Case 4 : t ≡ 𝐒 𝐒 a, return 𝐒 (h (𝐒 a)).
    --h'' t (inj₂ ( inj₂ ( inj₂ ( inj₁ (a , refl))))) = 𝐒 (h'' (𝐒 a) (double-pama-lemma (𝐒 a)))
    ---- Case 5 : t ≡ 𝐒 𝐏 a, apply inversity; return (h a).
    --h'' t (inj₂ ( inj₂ ( inj₂ ( inj₂ ( inj₁ (a , refl)))))) = h'' a (double-pama-lemma a)
    ---- Case 6 : t ≡ 𝐏 𝐒 a, apply inversity; return (h a).
    --h'' t (inj₂ ( inj₂ ( inj₂ ( inj₂ ( inj₂ ( inj₁ (a , refl))))))) = h'' a (double-pama-lemma a)
    ---- Case 7 : t ≡ 𝐏 𝐏 a, apply inversity; return 𝐏 (h (𝐏 a)).
    --h'' t (inj₂ ( inj₂ ( inj₂ ( inj₂ ( inj₂ ( inj₂ (a , refl))))))) = 𝐏 (h'' (𝐏 a) (double-pama-lemma ( 𝐏 a)))

    --h : C → C
    --h t = h' t (double-pama-lemma t)
    --    module HDef where
    --        -- Unfortunatelty, Agda requires me to write out the full stack
    --        -- of injections here; the macros case1, case2, case3, etc.
    --        -- are not allowed in pattern matching...
    --        -- #TODO: maybe the rigth `syntax` declaration will be allowed?
    --        -- For lists we can use the _∷_ notation, was that not syntax?
    --        h' : (t : C) → PaMaCases t → C
    --        -- Case 1 : t ≡ 𝟎
    --        h' t (inj₁ refl) = t
    --        -- Case 2 : t ≡ 𝐒 𝟎, which is already normal.
    --        h' t (inj₂ (inj₁ refl)) = t
    --        -- Case 3 : t ≡ 𝐏 𝟎, which is already normal.
    --        h' t (inj₂ ( inj₂ ( inj₁ refl))) = t
    --        -- Case 4 : t ≡ 𝐒 𝐒 a, return 𝐒 (h (𝐒 a)).
    --        h' t (inj₂ ( inj₂ ( inj₂ ( inj₁ (a , refl))))) = 𝐒 (h (𝐒 a))
    --        -- Case 5 : t ≡ 𝐒 𝐏 a, apply inversity; return (h a).
    --        h' t (inj₂ ( inj₂ ( inj₂ ( inj₂ ( inj₁ (a , refl)))))) = h a
    --        -- Case 6 : t ≡ 𝐏 𝐒 a, apply inversity; return (h a).
    --        h' t (inj₂ ( inj₂ ( inj₂ ( inj₂ ( inj₂ ( inj₁ (a , refl))))))) = h a
    --        -- Case 7 : t ≡ 𝐏 𝐏 a, apply inversity; return 𝐏 (h (𝐏 a)).
    --        h' t (inj₂ ( inj₂ ( inj₂ ( inj₂ ( inj₂ ( inj₂ (a , refl))))))) = 𝐏 (h (𝐏 a))

    --        -- Note about case 4 and case 7: if we were to define
    --        -- h (𝐒 𝐒 a) := 𝐒 𝐒 (h a)
    --        -- then 
    --        -- h(𝐒 𝐒 𝐏 𝟎) ≗ 𝐒 𝐒 (h (𝐏 𝟎)) ≗ 𝐒 𝐒 𝐏 𝟎  ≠ 𝐒 𝟎

    --h-fix
    --    : (t : C)
    --    → h (h t) ≡ h t
    --h-fix t = h-fix' t (double-pama-lemma t)
    --    where
    --    h-fix' : (t : C) → PaMaCases t → h (h t) ≡ h t
    --    -- Case 1 : t ≡ 𝟎
    --    h-fix' t (inj₁ refl) = 
    --        ≡begin 
    --            h (h 𝟎) 
    --        ≡⟨ cong h lemma ⟩
    --            h 𝟎
    --        ≡∎
    --        where
    --            --module Meh = HDef 𝟎
    --            --open Meh
    --            lemma : h 𝟎 ≡ 𝟎
    --            lemma = 
    --                ≡begin 
    --                    h 𝟎
    --                ≡⟨ ? ⟩
    --                    HDef.h' 𝟎 𝟎 (double-pama-lemma 𝟎)
    --                ≡⟨⟩ 
    --                    HDef.h' 𝟎 𝟎 (inj₁ refl)
    --                ≡⟨ ? ⟩
    --                    𝟎
    --                ≡∎
                

    --    -- Case 2 : t ≡ 𝐒 𝟎
    --    h-fix' t (inj₂ (inj₁ refl)) = ?
    --    -- Case 3 : t ≡ 𝐏 𝟎
    --    h-fix' t (inj₂ ( inj₂ ( inj₁ refl))) = ?
    --    -- Case 4 : t ≡ 𝐒 𝐒 a, return 𝐒 (h-fix (𝐒 a)).
    --    h-fix' t (inj₂ ( inj₂ ( inj₂ ( inj₁ (a , refl))))) = {! 𝐒 (h-fix (𝐒 a)) !}
    --    -- Case 5 : t ≡ 𝐒 𝐏 a, apply inversity; return (h-fix a).
    --    h-fix' t (inj₂ ( inj₂ ( inj₂ ( inj₂ ( inj₁ (a , refl)))))) = {! h-fix a !}
    --    -- Case 6 : t ≡ 𝐏 𝐒 a, apply inversity; return (h-fix a).
    --    h-fix' t (inj₂ ( inj₂ ( inj₂ ( inj₂ ( inj₂ ( inj₁ (a , refl))))))) = {! h-fix a !}
    --    -- Case 7 : t ≡ 𝐏 𝐏 a, apply inversity; return 𝐏 (h-fix (𝐏 a)).
    --    h-fix' t (inj₂ ( inj₂ ( inj₂ ( inj₂ ( inj₂ ( inj₂ (a , refl))))))) = {! 𝐏 (h-fix (𝐏 a)) !}

    --g-fix : (t : C) → g (g t) ≡ g t
    --g-fix t = g-fix' t (pama-lemma t)
    --    where
    --        g-fix' : (t : C) → SinglePaMaCases t → g (g t) ≡ g t
    --        g-fixₛ  : (t a : C) 
    --            → (t ≡ 𝐒 a)
    --            → SinglePaMaCases a
    --            → g (g t) ≡ g t
    --        g-fixₚ  : (t a : C) 
    --            → (t ≡ 𝐏 a)
    --            → SinglePaMaCases a
    --            → g (g t) ≡ g t

    --        g-fix' 𝟎 (inj₁ refl) = {! refl !}
    --        g-fix' t (inj₂ (inj₁ (a , refl))) = g-fixₛ t a refl (pama-lemma a)
    --        g-fix' t (inj₂ (inj₂ (a , refl))) = g-fixₚ t a refl (pama-lemma a)

    --        -- Case 1 : t ≡ 𝐒 𝟎, which is already normal.
    --        g-fixₛ t a refl (inj₁ refl) = ?
    --        -- Case 2 : t ≡ 𝐒 𝐒 a'
    --        g-fixₛ t a refl (inj₂ (inj₁  (a' , refl))) = ?
    --        -- Case 3 : t ≡ 𝐒 𝐏 a'; inversity applies, so return (g a')
    --        g-fixₛ t a refl (inj₂ ( inj₂ (a' , refl))) = ?
    --        -- Case 4 : t ≡ 𝐏 𝟎, which is already normal.
    --        g-fixₚ t a refl (inj₁ refl) = ?
    --        -- Case 5 : t ≡ 𝐏 𝐒 a'; inversity applies, so return g a'
    --        g-fixₚ t a refl (inj₂ (inj₁  (a' , refl))) = ?
    --        -- Case 6 : t ≡ 𝐏 𝐏 a'; return (g a')
    --        g-fixₚ t a refl (inj₂ ( inj₂ (a' , refl))) = ?
    --... | inj₁ t≡𝟎 = refl
    --... | inj₂ (inj₂ (a , t≡𝐏a)) = {! !}
    ---- Case t ≡ 𝐒 a
    --... | inj₂ (inj₁ (a , refl)) with pama-lemma a
    ---- Subcase t ≡ 𝐒 𝟎
    --...     | inj₁ refl = ?
    ---- Subcase t ≡ 𝐒 𝐒 a'. 
    --...     | inj₂ (inj₁ (a' , refl)) =
    --        let gga'≡ga' : g (g a') ≡ g a'
    --            gga'≡ga' = g-fix a'
    --            in
    --            -- # TODO: Agda doesn't see that g (𝐒 (𝐒 a')) ≗ 𝐒 (𝐒 (g a'))
    --            {! cong (λ x → 𝐒 (𝐒 x)) gga'≡ga' !}
    ---- Subcase t ≡ 𝐒 𝐏 a'. Then g (𝐒 𝐏 a') ≗ a', so apply the induction hyp:
    --...     | inj₂ (inj₂ (a' , refl)) = g-fix a'

    open EnumLifts {C} C≃ℕ

    --nf : ℕ → ℕ
    --nf = elift nf'

    --nf-leq : NFLeq nf
    --nf-leq = elift-leq nf' nf'-leq

    --nf-fix : NFFix nf
    --nf-fix = {! elift-fix nf' nf'-fix!}

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

ℤ : Set
ℤ = ?

ℤcorrectness : ℤ ≃ StdlibInt.ℤ
ℤcorrectness = ?
