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
--------------------------------------------------------------------------------

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
open import Eser.Signature.NoWeight

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

    --------------------------------------------------------------------------------
    -- Normal-form function
    --------------------------------------------------------------------------------
    -- *Intuitively*, the function should simply be this:
    nf' : ℤ' → ℤ'
    nf' O = O
    nf' (S O) = S O
    nf' (P O) = P O
    nf' (S (P t)) = nf' t
    nf' (P (S t)) = nf' t
    nf' (S (S t)) = S $ nf' $ S t
    nf' (P (P t)) = P $ nf' $ P t

    -- THIS IS WRONG!
    counterexample : nf' (S $ S $ P $ P O) ≡ (S $ P O)
    counterexample = refl

    -- I implement this function below, but rewrote the `with` clauses
    -- into explicit functions to make it easier to prove things about it:
    f' : ℤ' → ℤ'
    f' O = O
    f' (S z) with f' z
    ... | O = S O
    ... | S z' = S (S z')
    ... | P z' = z'
    f' (P z) with f' z
    ... | O = P O
    ... | S z' = z'
    ... | P z' = P (P z')

    -- First 'with' clause of f, when the input is S z.
    f-Sz : ℤ' → ℤ'
    f-Sz O = S O
    f-Sz (S z') = S (S z')
    f-Sz (P z') = z'
    -- Second 'with' clause of f, when the input is P z.
    f-Pz : ℤ' → ℤ'
    f-Pz O = P O
    f-Pz (S z') = z'
    f-Pz (P z') = P (P z')
    -- Actual top-level function.
    f : ℤ' → ℤ'
    f O = O
    f (S z) = f-Sz (f z)
    f (P z) = f-Pz (f z)

    module IsCleanPredicates where
        IsZero : ℤ' → Set
        IsZero O = ⊤
        IsZero (S z) = ⊥
        IsZero (P z) = ⊥

        IsPos : ℤ' → Set
        IsPos O = ⊥
        IsPos (S O) = ⊤
        IsPos (S (S z)) = IsPos (S z)
        IsPos (S (P z)) = ⊥
        IsPos (P z) = ⊥

        IsNeg : ℤ' → Set
        IsNeg O = ⊥
        IsNeg (S z) = ⊥
        IsNeg (P O) = ⊤
        IsNeg (P (P z)) = IsNeg (P z)
        IsNeg (P (S z)) = ⊥

        IsClean : ℤ' → Set
        IsClean z = IsZero z ⊎ IsPos z ⊎ IsNeg z

        f-Sz-presv-cleanness
            : (z : ℤ')
            → IsClean z
            → IsClean (f-Sz z)
        f-Sz-presv-cleanness O (inj₁ tt) = inj₂ $ inj₁ tt
        f-Sz-presv-cleanness O (inj₂ (inj₁ ()))
        f-Sz-presv-cleanness O (inj₂ (inj₂ ()))
        f-Sz-presv-cleanness (S O) (inj₂ (inj₁ tt)) = inj₂ $ inj₁ tt
        f-Sz-presv-cleanness (S (S z)) (inj₂ (inj₁ x)) = inj₂ $ inj₁ x
        f-Sz-presv-cleanness (P O) (inj₂ (inj₂ tt)) = inj₁ tt
        f-Sz-presv-cleanness (P (P z)) (inj₂ (inj₂ y)) = inj₂ $ inj₂ y

        f-Pz-presv-cleanness
            : (z : ℤ')
            → IsClean z
            → IsClean (f-Pz z)
        f-Pz-presv-cleanness O (inj₁ tt) = inj₂ $ inj₂ tt
        f-Pz-presv-cleanness O (inj₂ (inj₁ ()))
        f-Pz-presv-cleanness O (inj₂ (inj₂ ()))
        f-Pz-presv-cleanness (P O) (inj₂ (inj₂ tt)) = inj₂ $ inj₂ tt
        f-Pz-presv-cleanness (P (P z)) (inj₂ (inj₂ x)) = inj₂ $ inj₂ x
        f-Pz-presv-cleanness (S O) (inj₂ (inj₁ tt)) = inj₁ tt
        f-Pz-presv-cleanness (S (S z)) (inj₂ (inj₁ y)) = inj₂ $ inj₁ y

        is-clean-S-downgrade
            : {z : ℤ'}
            → IsClean (S z)
            → IsClean z
        is-clean-S-downgrade {O} k@(inj₂ (inj₁ tt)) = inj₁ tt
        is-clean-S-downgrade {S z} k@(inj₂ (inj₁ x)) = k

        is-clean-P-downgrade
            : {z : ℤ'}
            → IsClean (P z)
            → IsClean z
        is-clean-P-downgrade {O} k@(inj₂ (inj₂ tt)) = inj₁ tt
        is-clean-P-downgrade {P z} k@(inj₂ (inj₂ x)) = k

        f-presv-cleanness 
            : (z : ℤ')
            → IsClean z
            → IsClean (f z)
        f-presv-cleanness O (inj₁ tt) = inj₁ tt
        f-presv-cleanness O (inj₂ (inj₁ ()))
        f-presv-cleanness O (inj₂ (inj₂ ()))
        f-presv-cleanness (S z) k@(inj₂ (inj₁ x)) = 
            f-Sz-presv-cleanness (f z) IH
            where
                IH : IsClean (f z)
                IH = f-presv-cleanness z (is-clean-S-downgrade k)
        f-presv-cleanness (P z) k@(inj₂ (inj₂ x)) = 
            f-Pz-presv-cleanness (f z) IH
            where
                IH : IsClean (f z)
                IH = f-presv-cleanness z (is-clean-P-downgrade k)

        f-cleans : (z : ℤ') → IsClean (f z)
        f-cleans O = inj₁ tt
        f-cleans (S z) = f-Sz-presv-cleanness (f z) IH
            where 
                IH : IsClean (f z)
                IH = f-cleans z
        f-cleans (P z) = f-Pz-presv-cleanness (f z) IH
            where 
                IH : IsClean (f z)
                IH = f-cleans z

    open IsCleanPredicates

    f-fixes-on-clean-inp : (z : ℤ') → IsClean z → f z ≡ z
    f-fixes-on-clean-inp O k = refl
    f-fixes-on-clean-inp (S O) (inj₂ (inj₁ tt)) = refl
    f-fixes-on-clean-inp (S (S z)) k@(inj₂ (inj₁ x)) = 
        ≡begin 
            f (S (S z))
        ≡⟨⟩
            f-Sz (f (S z))
        ≡⟨ cong f-Sz $ f-fixes-on-clean-inp (S z) (is-clean-S-downgrade {S z} k) ⟩
            f-Sz (S z)
        ≡⟨⟩
            S (S z)
        ≡∎
    f-fixes-on-clean-inp (P O) (inj₂ (inj₂ tt)) = refl
    f-fixes-on-clean-inp (P (P z)) k@(inj₂ (inj₂ x)) =
        ≡begin 
            f (P (P z))
        ≡⟨⟩
            f-Pz (f (P z))
        ≡⟨ cong f-Pz $ f-fixes-on-clean-inp (P z) (is-clean-P-downgrade {P z} k) ⟩
            f-Pz (P z)
        ≡⟨⟩
            P (P z)
        ≡∎

    f-fix : (z : ℤ') → f (f z) ≡ f z
    f-fix z = f-fixes-on-clean-inp (f z) (f-cleans z)

    --------------------------------------------------------------------------------
    -- Shorter-term relation ⊑ on ℤ'
    --
    -- The height of a term is the number of connectives.
    --------------------------------------------------------------------------------
    module ShorterTermOrder where
        _⊑_ : Rel ℤ' 0ℓ 
        O ⊑ O = ⊤
        O ⊑ S z = ⊤
        O ⊑ P z = ⊤

        S z ⊑ O = ⊥
        S z ⊑ S z' = z ⊑ z'
        S z ⊑ P z' = z ⊑ z'

        P z ⊑ O = ⊥
        P z ⊑ S z' = z ⊑ z'
        P z ⊑ P z' = z ⊑ z'

        S-mono : (z z' : ℤ') → z ⊑ z' → S z ⊑ S z'
        S-mono z z' z⊑z' = z⊑z'
        P-mono : (z z' : ℤ') → z ⊑ z' → P z ⊑ P z'
        P-mono z z' z⊑z' = z⊑z'
        S-increasing : (z z' : ℤ') → z ⊑ z' → z ⊑ S z'
        P-increasing : (z z' : ℤ') → z ⊑ z' → z ⊑ P z'

        S-increasing O z' z⊑z' = tt
        S-increasing (S z) (S z') z⊑z' = S-increasing z z' z⊑z'
        S-increasing (S z) (P z') z⊑z' = P-increasing z z' z⊑z'
        S-increasing (P z) (S z') z⊑z' = S-increasing z z' z⊑z'
        S-increasing (P z) (P z') z⊑z' = P-increasing z z' z⊑z'

        P-increasing O z' z⊑z' = tt
        P-increasing (S z) (S z') z⊑z' = S-increasing z z' z⊑z'
        P-increasing (S z) (P z') z⊑z' = P-increasing z z' z⊑z'
        P-increasing (P z) (S z') z⊑z' = S-increasing z z' z⊑z'
        P-increasing (P z) (P z') z⊑z' = P-increasing z z' z⊑z'

        ⊑-refl : (z : ℤ') → z ⊑ z
        ⊑-refl O = tt
        ⊑-refl (S z) = S-mono z z (⊑-refl z)
        ⊑-refl (P z) = P-mono z z (⊑-refl z)

        f-Sz-decreasing : (z : ℤ') → f-Sz z ⊑ S z
        f-Sz-decreasing O = tt
        f-Sz-decreasing (S z) = ⊑-refl z
        f-Sz-decreasing (P z) = 
            S-increasing z (P z) $ P-increasing z z $ ⊑-refl z

        f-Pz-decreasing : (z : ℤ') → f-Pz z ⊑ S z
        f-Pz-decreasing O = tt
        f-Pz-decreasing (S z) =
            S-increasing z (S z) $ S-increasing z z $ ⊑-refl z
        f-Pz-decreasing (P z) = ⊑-refl z

    open ShorterTermOrder

    f-leq : (z : ℤ') → f z ⊑ z
    f-leq O = tt
    f-leq (S z) = ?
    f-leq (P z) = ?



    -- #TODO: Comment below is outdated.
    -- So instead we define a normal-form function w : C → C on
    -- the no-weight representation of terms over ℤSig.
    -- This was tricky to implement, since we need to do nested pattern-matching
    -- (to get the cases S S t, P S t, S P t, P P t),
    -- which got Agda's termination checker really confused.
    -- It seems nested pattern-matching does not work as expected for *indexed*
    -- inductive types, and OT is still indexed by the number of open holes.
    --
    -- The solution
    -- Only do one layer of pattern-matching, and use an auxiliary function
    -- to perform the second match.
    -- Give the auxiliary function the data needed to reconstruct the original
    -- input term when needed (that's `t'`, see below).
    -- The function can be hard to read, but one can mentally use the following
    -- macros:
    𝟎 : C
    𝟎 = mk-nullary-nw Fin.zero

    𝐒 : C → C
    𝐒 = giveArg-nw $ mk-multiary-nw Fin.zero 

    {-# DISPLAY giveArg-nw (mk-multiary-nw Fin.zero) t = 𝐒 t #-}

    𝐏 : C → C
    𝐏 = giveArg-nw $ mk-multiary-nw $ Fin.suc Fin.zero

    w : C → C
    w' : OT 1 → OT 0 → OT 0
    -- Case t ≗ 𝟎. Just return 𝟎.
    w t@(mk-nullary-nw c) = t
    w (giveArg-nw t' a) = w' t' a
    -- Case t ≗ 𝐒 𝟎 xor t ≡ 𝐏 𝟎. This is already normal, just return t ≗
    -- giveArg-nw t' a. (Whether it is 𝐒 or 𝐏 depends on t').
    w' t' a@(mk-nullary-nw c) = giveArg-nw t' a
    w' t' a@(giveArg-nw t'' a') = 
        sublemma (decEquality {fin 1} {fin 2} ℤSig t' t'')
        module WImpl where
            sublemma : (q : Relation.Nullary.Dec (t' ≡ t''))
                → OT 0
            sublemma (yes refl) = giveArg-nw t' $ w' t'' a'
            sublemma (no t'≢t'') = w a'
    ---- Case t' ≡ t''. Then the original input is of the form P P a'
    ---- xor S S a'. So return P P (nf a') xor S S (nf a') respectively.
    --... | yes refl = giveArg-nw t' $ w' t'' a'
    ---- Case t' ≢ t''. Then the original input is of the form S P a'
    ---- xor P S a'. So apply inversity between S and P, and return: nf a'.
    --... | no  t'≢t'' = w a'
    --w' t' a@(giveArg-nw t'' a') with decEquality {fin 1} {fin 2} ℤSig t' t''
    ---- Case t' ≡ t''. Then the original input is of the form P P a'
    ---- xor S S a'. So return P P (nf a') xor S S (nf a') respectively.
    --... | yes refl = giveArg-nw t' $ w' t'' a'
    ---- Case t' ≢ t''. Then the original input is of the form S P a'
    ---- xor P S a'. So apply inversity between S and P, and return: nf a'.
    --... | no  t'≢t'' = w a'

    open WImpl

    w-fix
        : (t : C)
        → w (w t) ≡ w t
    w'-fix
        : (t' : OT 1)
        → (a : OT 0)
        → w (w' t' a) ≡ w (giveArg-nw t' a)
    w-fix (mk-nullary-nw c) = refl
    w-fix (giveArg-nw t' a) = w'-fix t' a
    w'-fix t' a@(mk-nullary-nw c) = refl
    --w'-fix t' a@(giveArg-nw t'' a') = sublemma $ decEquality {fin 1} {fin 2} ℤSig t' t''
    --    where
    --        sublemma 
    --            : (q : Relation.Nullary.Dec (t' ≡ t''))
    --            → decEquality {fin 1} {fin 2} ℤSig t' t'' ≡ q
    --            → w (w' t' a) ≡ w (giveArg-nw t' a)
    --        sublemma q refl = 
    --            ≡begin 
    --                w (w' t' (giveArg-nw t' a') )
    --            ≡⟨⟩
    --                w (giveArg-nw t' $ w' t'' a')
    --            ≡⟨ ? ⟩
    --               (w' t' (giveArg-nw t' a') )
    --            ≡∎
    --        sublemma (no t'≢t'') refl = ?
    --... | no t'≢t'' = ?
    w'-fix t' a@(giveArg-nw t'' a') with (decEquality {fin 1} {fin 2} ℤSig t' t'')
    -- Case t' ≡ t''. Then the original input is of the form P P a'
    -- xor S S a'. 
    ... | yes refl = 
        let H : sublemma t' t' a' (yes refl) ≡ giveArg-nw t' (w' t'' a')
            H = refl
        in 
        ≡begin 
            w (sublemma t' t' a' (yes refl))
        ≡⟨⟩
            w (giveArg-nw t' ( w' t'' a'))
        ≡⟨⟩
            w (giveArg-nw t' ( w (giveArg-nw t'' a')))
        ≡⟨ cong (λ x → w (giveArg-nw t' x)) $ sym $ w'-fix t'' a' ⟩
            w (giveArg-nw t' ( w (w' t'' a')))
        ≡⟨ ? ⟩  -- cong w-fix !
            w (giveArg-nw t' (w' t'' a'))
            -- Eh we have a circle now...
        ≡⟨ ? ⟩
            sublemma t' t' a' (yes refl)
        ≡⟨⟩
            giveArg-nw t' ( w' t'' a')
        --≡⟨⟩
        --    w ( giveArg-nw t' a)
        ≡∎
        
    -- Case t' ≢ t''. Then the original input is of the form S P a'
    -- xor P S a'. So apply inversity between S and P, and return: nf a'.
    ... | no  t'≢t''  = ?

          
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

-- #EXT: Add addition?
