-- Module      : Eser.Filters.Closure.Single
-- Description : Properties of closing w.r.t. a single filter.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- For properties specific to closures w.r.t. compositions of filters, see
-- Eser.Filters.Closure.Composed instead.
--------------------------------------------------------------------------------

--{-# OPTIONS --safe #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Relation.Binary.Definitions 
    using (Tri ; Reflexive ; Symmetric ; Transitive ; DecidableEquality)
open Tri
open import Relation.Nullary
open import Relation.Nullary.Decidable
open import Data.Product
open import Data.Sum
open import Function using (_∘_ ; _$_ ; id)
open import Data.List using (List ; [] ; _∷_)
open import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.Any.Properties

open import Eser.EqRel.Definitions
open import Eser.EqRel.Conversions
open import Eser.EqRel.Correspondences
open import Eser.EqRel.EqRelProperties
open import Eser.Aux using 
    ( _≈_ 
    ; _≈≈_ 
    ; _↔_ 
    ; ↔-to 
    ; ↔-from 
    ; ↔-trans 
    ; doubleCong
    ; ≡→↔
    )
open import Eser.Logic using
    ( ≡→≡ᵇ
    ; does-toWitness
    )
open import Eser.Relation.Binary.Path

open import Eser.Filters.Conversions.NFFunToExence
open import Eser.Filters.Base
open import Eser.Filters.Properties
open import Eser.Filters.PointwiseProperties
open import Eser.Filters.Resurface
open import Eser.Filters.Composition
open _closure-of_

module Eser.Filters.Closure.Single where

--------------------------------------------------------------------------------
-- Preliminary/auxiliary lemmas
--------------------------------------------------------------------------------

-- Get the F-closure of R represented in the form of an Exence.
exclosure
    : {F : Filter}
    → (C : IsClosable F)
    → (R : EqRel)
    → Exence
exclosure C R = rel-to-exence $ rel (C R)

get-unique-choice-exence
    : {F : MFF}
    → (C : IsClosable' F)
    → (AF : AlwaysFires F)
    → (R : EqRel)
    → (y : ℕ)
    → getChoiceFromExence (exclosure C R) y 
      ≡ 
      (proj₁ $ get-unique-choice C AF (proj₁ (exclosure C R) y))
get-unique-choice-exence = ?

--------------------------------------------------------------------------------
-- Conversion lemma between Exence and EqRel version of main theorem
--------------------------------------------------------------------------------
-- Also used as sublemma within the proofs.

ConversionStatement
    : (E : EqFilter)
    → (R : EqRel)
    → Set
ConversionStatement E R = (x y : ℕ) → (S relates x to y) ↔ (ExRel hH x y)
    where
        F : Filter
        F = EqFilter→Filter E
        C : IsClosable F
        C = EqFilter-IsClosable E
        hH : Exence
        hH = rel-to-exence $ rel (C R)
        S : EqRel
        S = rel (C R)

-- Pointwise conversion from the Exence representation
-- to the EqRel representation of a closure.
closure-exence-to-eqrel
    : (E : EqFilter)
    → (R : EqRel)
    → ConversionStatement E R
closure-exence-to-eqrel E R x y = ≡→↔ $ sym $ eq x y
    where
        F : Filter
        F = EqFilter→Filter E
        C : IsClosable F
        C = EqFilter-IsClosable E
        hH : Exence
        hH = rel-to-exence $ rel (C R)
        S : EqRel
        S = rel (C R)

        open ≡-Reasoning

        S'' : ℕ → ℕ → Bool
        S'' = proj₁ $ (FunToRel ∘ combine ∘ restrict+ ∘ RelToFun) S

        eq : (x y : ℕ)
           → ExRel hH x y ≡ S relates x to y 
        eq x y = 
            begin 
                ExRel hH x y 
            ≡⟨⟩
                ((FunToRel ∘ combine) hH) relates x to y
            ≡⟨⟩
                ((FunToRel ∘ combine ∘ restrict+ ∘ RelToFun) S) relates x to y
            ≡⟨⟩
                T (S'' x y) 
            ≡⟨ cong T $ eqrel-exence-round-trip S x y ⟩ 
                T (proj₁ S x y) 
            ≡⟨⟩
                S relates x to y
            ∎

--------------------------------------------------------------------------------
-- 𝐓𝐡𝐞𝐨𝐫𝐞𝐦
-- The F-closure of R is the same thing as the unique relation satisfying
-- the filter `(filterify' R) » F`.
-- This gives a way of computing the closure.
--------------------------------------------------------------------------------
toMove : Set
toMove = {! TODO: move to more appropriate file? !}

closureFilter
    : (F : MFF)
    → (R : EqRel)
    → MFF
closureFilter F R = (EqRel→MFF R) » F

closure-implementation
    : {F : MFF}
    → (R : EqRel)
    → {S : EqRel}
    → DeadEndFree' F
    → IsOneHot' F
    → NeverForcesnewNF' F
    → (S is-the F closure-of R) ↔ (Rel-sats' (closureFilter F R) S)
closure-implementation {F} R {S} DEF OH NFN = ?

-- Given an MFF composition G » F and an input r : NFRestr n
-- on which we know F r doesn't and G r does fire,
-- then any Exence containing r that satisfies G » F must
-- contain one of the choices that G allows at r.
»-second-fires
    : {G F : MFF}
    → (h : (n : ℕ) → NFRestr n)
    → (H : (n : ℕ) → h n ⋖ h (suc n))
    → {y : ℕ}
    → IsPass (F (h y))
    → IsFire (G (h y))
    → Exence-sats (MFF→Filter (G » F)) (h , H)
    → G allows' (getChoiceFromExence (h , H) y) to (h y)
»-second-fires = ?


Filter→MFF→Filter
    : (F : Filter)
    → (MFF→Filter (Filter→MFF F)) ≈ F
Filter→MFF→Filter = ?

UniqueChoice : MFF → Set
UniqueChoice F = 
      {n : ℕ}
    → (r : NFRestr n)
    → Σ[ c ∈ Choices r ] (
                         F allows' c to r
                         × 
                         ((c' : Choices r) → (F allows' c' to r) → c' ≡ c)
                         )

-- When converting a relation to a filter, one obtains a filter that allows
-- exactly one choice to each input NFRestr.
eqrel-uniquechoice
    : (R : EqRel)
    → UniqueChoice (EqRel→MFF R)
eqrel-uniquechoice R {n} r = (c , p , u)
    where
        f' : NFFun
        f' = RelToFun R
        f : ℕ → ℕ
        f = proj₁ f'
        f-leq : (n : ℕ) → f n ≤ n
        f-leq = proj₁ $ proj₂ f'
        
        F : MFF
        F = EqRel→MFF R
        c : Choices r
        c = resurface' r (f-leq n)
        open MFF→FilterImpl F r c renaming (cases to mff2filt-cases)
        open OneHot→MFFImpl (NFFun→OneHot f') r renaming (cases to oh2mff-cases)
        p : F allows' c to r
        p = 
            begin 
                MFF→Filter (EqRel→MFF R) r c
            ≡⟨⟩
                (MFF→Filter ∘ NFFun→MFF ∘ RelToFun) R r c
            ≡⟨⟩
                (MFF→Filter ∘ OneHot→MFF ∘ NFFun→OneHot) f' r c
            ≡⟨⟩
                mff2filt-cases (OneHot→MFF (NFFun→OneHot f') r) c
            ≡⟨⟩
                mff2filt-cases (oh2mff-cases ((NFFun→OneHot f') r)) c
            ≡⟨⟩ -- Definition NFFun→OneHot:
                mff2filt-cases (oh2mff-cases (fire c)) c
            ≡⟨⟩ -- Definition oh2mff-cases:
                mff2filt-cases (fire $ λ c' → does (c ≡? c') ) c
            ≡⟨⟩ -- Definition mff2filt-cases
                does (c ≡? c)
            ≡⟨ dec-true (c ≡? c) refl ⟩
                true
            ∎
            
        u : (c' : Choices r) → F allows' c' to r → c' ≡ c
        u c' prf = sym $ does-toWitness (c ≡? c') prf'
            where
                -- prf normalises to this:
                prf' : does (c ≡? c') ≡ true
                prf' = prf

-- Special case of previous lemma: if we also know that G allows exactly
-- one choice at r, then that must be the choice the Exence makes as well.
»-second-fires-unique
    : {G F : MFF}
    → (h : (n : ℕ) → NFRestr n)
    → (H : (n : ℕ) → h n ⋖ h (suc n))
    → {y : ℕ}
    → IsPass (F (h y))
    → (u : UniqueChoice G)
    → Exence-sats' (G » F) (h , H)
    → getChoiceFromExence (h , H) y ≡ proj₁ (u (h y))
»-second-fires-unique = ?

-- If an Exence makes the choice newNF at y,
-- then y is made the smallest element of a new equivalence class.
-- Later numbers added to this class are greater than y.
-- So there cannot be a smaller number x < y that the Exence relates to y,
-- since it cannot be added to this equivalence class.
newNF-not-related-to-smaller
    : (hH : Exence)
    → {x y : ℕ}
    → getChoiceFromExence hH y ≡ here
    → x < y
    → ExRel hH x y
    → ⊥
newNF-not-related-to-smaller = ?

--------------------------------------------------------------------------------
-- 𝐓𝐡𝐞𝐨𝐫𝐞𝐦
-- Characterisation of a closure of a relation w.r.t. an EqFilter.
--
--------------------------------------------------------------------------------
-- Proof stategy: we first prove it for the Exence corresponding to the closure,
-- because this representation is much closer to filters and the construction of
-- the relation.
-- Then we lift the result via the canonical conversions to EqRel.
--------------------------------------------------------------------------------

get-closure-as-exence 
    : (E : EqFilter)
    → (R : EqRel)
    → Exence
get-closure-as-exence E R = rel-to-exence $ rel (C R)
    where
        C : IsClosable (EqFilter→Filter E)
        C = EqFilter-IsClosable E

-- Statement of next lemma.
ClosureExBiimpl
    : (E : EqFilter)
    → (R : EqRel)
    → Set
ClosureExBiimpl E R = 
      (x y : ℕ)
    → (ExRel (get-closure-as-exence E R) x y)
      ↔
      (Path (R relates_to_) (Eq E) x y )

eqfilter-passes
    : (E : EqFilter)
    → {y : ℕ}
    → IsPass (E y)
    → (r : NFRestr y)
    → IsPass (EqFilter→MFF E r)
eqfilter-passes E {y} eq r = 
    begin 
        EqFilter→MFF E r
    ≡⟨⟩
        OneHot→MFF (EqFilter→OneHot E) r
    ≡⟨⟩
        OH-cases (EqFilter→OneHot E r)
    ≡⟨⟩
        OH-cases (EF-cases (E y))
    ≡⟨ cong (OH-cases ∘ EF-cases) eq ⟩
        OH-cases (EF-cases pass)
    ≡⟨⟩
        OH-cases pass
    ≡⟨⟩
        pass
    ∎
    where
    open ≡-Reasoning
    open OneHot→MFFImpl (EqFilter→OneHot E) r renaming (cases to OH-cases)
    open EqFilterToOneHotImpl E r renaming (cases to EF-cases)
    

-- Implementation of the next theorem.
-- Just to reduce number of arguments to pass around and things
-- to redefine every time.
module EqfilClosureCharExenceImpl (E : EqFilter) (R : EqRel) where
    open ≡-Reasoning

    F : Filter
    F = EqFilter→Filter E
    F' : MFF
    F' = EqFilter→MFF E
    G' : MFF
    G' = EqRel→MFF R
    C : IsClosable F
    C = EqFilter-IsClosable E
    hH : Exence
    hH = rel-to-exence $ rel (C R)
    h : (n : ℕ) → NFRestr n
    h = proj₁ hH
    H : (n : ℕ) → h n ⋖ h (suc n)
    H = proj₂ hH
    R⊆S : R ⊆ (rel (C R))
    R⊆S = ext (C R)
    R⊆hH : {x y : ℕ} → R relates x to y → ExRel hH x y
    R⊆hH {x} {y} xRy = ↔-to (closure-exence-to-eqrel E R x y) (R⊆S x y xRy)

    -- Case in which E does not contain an equality with y as LHS,
    -- i.e., when the associated MFF did not fire.
    -- The the filter associated with R did still fire,
    -- forcing hH to normalise y the same way as R does.
    -- Let m ≤ y be the normal form that R assigns to y.
    --
    -- If x ≡ m, then mRy is already the desired path.
    --
    -- If m ≡ y, we obtain a contradiction, since x hH y
    -- is only possible if the normal form of y (acc. to hH) is smaller than y,
    -- which would not be the case if hH inherits the normalisation y => y
    -- from R.
    --
    -- If x < m < y or m < x, w.l.o.g. say x < m,
    -- then trans+sym of hH gives x hH m,
    -- then a well-founded recursive call (on m < y) gives a path x ⇝ m,
    -- and we add m R y as last step to finish.
    to-<-nofire
        : {x y m : ℕ}
        → x < y
        → IsPass (E y)
        → m ≡ (proj₁ $ RelToFun R) y
        → ExRel hH x y
        → Path (R relates_to_) (Eq E) x y
    to-<-nofire {x} {y} {m} x<y passes eq-m = to-<-nofire-cases (<-cmp x m)
            where   
            f' : NFFun
            f' = RelToFun R
            f : ℕ → ℕ
            f = proj₁ f'
            f-fix : (z : ℕ) → f (f z) ≡ f z
            f-fix = proj₂ $ proj₂ f'
            fm≡m : f m ≡ m
            fm≡m = 
                begin 
                    f m
                ≡⟨ cong f $ eq-m  ⟩
                    f (f y)
                ≡⟨ f-fix y ⟩
                    f y
                ≡⟨ sym eq-m ⟩
                    m
                ∎
                
            R' : EqRel
            R' = FunToRel f'
            mR'y : R' relates m to y
            mR'y = subst id (sym eq) tt
                where
                eq : R' relates m to y ≡ ⊤
                eq = begin 
                        R' relates m to y
                    ≡⟨⟩
                        T (f m ≡ᵇ f y)
                    ≡⟨ cong (λ z → T (f m ≡ᵇ z)) $ sym eq-m ⟩
                        T (f m ≡ᵇ m)
                    ≡⟨ cong (λ z → T (z ≡ᵇ m)) $ fm≡m  ⟩
                        T (m ≡ᵇ m)
                    ≡⟨ cong T (≡→≡ᵇ m m refl) ⟩
                        ⊤
                    ∎
                
                    
            mRy : R relates m to y
            mRy = subst id (sym eq) mR'y
                where
                eq : R relates m to y ≡ R' relates m to y
                eq = 
                    begin 
                        R relates m to y
                    ≡⟨⟩
                        T (proj₁ R m y)
                    ≡⟨ cong T $ sym $ RFRHomot R (m , y) ⟩
                        T (proj₁ R' m y)
                    ≡⟨⟩
                        R' relates m to y
                    ∎
            to-<-nofire-cases
                : Tri (x < m) (x ≡ m) (x > m)
                → ExRel hH x y
                → Path (R relates_to_) (Eq E) x y
            to-<-nofire-cases (tri≈ _ refl _) xhHy = step (inj₁ mRy) $ empty y 
                        
            to-<-nofire-cases (tri< x<m _ _) xhHy = ans
                where
                    m<y : Tri (m < y) (m ≡ y) (m > y) → m < y
                    m<y (tri< m<y _ _ ) = m<y
                    m<y (tri≈ _ m≡y _) = 
                        ⊥-elim $ newNF-not-related-to-smaller hH choice x<y xhHy
                        where
                            uniq : UniqueChoice G'
                            uniq {n} r = ?
                            e-sat : Exence-sats' (closureFilter F' R) hH
                            e-sat = ?

                            
                            choice : getChoiceFromExence hH y ≡ here
                            choice = 
                                begin 
                                    getChoiceFromExence hH y
                                ≡⟨ »-second-fires-unique {G'} {F'}
                                   h H (eqfilter-passes E {y} passes (h y)) uniq e-sat ⟩
                                    proj₁ (uniq (h y))
                                ≡⟨ ? ⟩
                                    here
                                ∎
                                
                            mhHy : ExRel hH m y
                            mhHy = ?

                    m<y (tri> _ _ y<m) = {! f-leq !}

                    mhHy : ExRel hH m y
                    mhHy = R⊆hH mRy 

                    rec : Path (R relates_to_) (Eq E) x m
                    rec = {! well-founded recursive call using m<y (<-cmp m y) on mhHy !}

                    ans = add-last-step (R relates_to_) (Eq E) rec (inj₁ mRy)

                

            to-<-nofire-cases (tri> _ _ m<x) xhHy = ?
            
    -- The only difficult case of `to` is when x < y.
    -- When x ≡ y we can return an empty path,
    -- and y < x is symmetric to the x < y case.
    -- (See `to` below for this case distinction).
    to-< 
        : {x y : ℕ}
        → x < y
        → (p : MayFire (Σ[ m ∈ ℕ ] m < y ))
        → p ≡ E y
        → ExRel hH x y
        → Path (R relates_to_) (Eq E) x y
    to-< {x} {y} x<y pass eq xhHy = ?
        -- Make a case distinction on the normal form of y according
        -- to R. It is some m ≤ y such that m R y.
        --
        -- The case m ≡ y leads to a contradiction.
        -- hH satisfies F_R » E' 
        -- (where F_R ≔ filterify R and E' ≔ EqFilter→MFF E), 
        -- but we are in the case where E did not 
        -- fire on input (h y), and F_R always fires,
        -- so the choice that moves (h y) to (h 1+y) is the unique
        -- choice F_R allows. Since m ≡ y, this choice can only be
        -- `newNF`. However, x hH y means that the normal form of y
        -- equals the normal form of x ≢ y, which is only possible
        -- if this choice is NOT `newNF`.
        -- So this choice is both equal and inequal to `newNF`:
        -- contradiction.
        --
        -- If x ≡ m < y then return the singleton path m R y.
        --
        -- If x < m, then R ⊆ hH implies m hH y,
        -- and by transitivity & symmetry of hH we obtain 
        -- also x hH m. A well-founded recursive call gives
        -- a Path x m (allowed since m < y). 
        -- Composing this with the singleton path 
        -- of mRy gives the desired result.
        --
        -- The case m < x is symmetric to the previous one,
        -- noting that also x < y holds.
    to-< {x} {y} x<y (fire (m , m<y)) eq xhHy = ?
        -- In this case, the EqFilter fired on input y
        -- and forced the NF of y to be the same as the NF of m.
        -- So we have m E y.
        -- Since hH sats the EqFilter, it follows that hH related m
        -- and y: m hH y.
        --
        -- If x ≡ m then return singleton path m E y.
        --
        -- Otherwise, w.l.o.g. assume x < m.
        -- Since hH is transitive and symmetric and x hH y
        -- we obtain also x hH m.
        -- Since m < y we can make a well-founded recursive call
        -- to obtain a Path x m. Apply path-trans with the m E y
        -- singleton path to obtain the desired result
        -- (or use path-sym , addstep, and path-sym again).
        -- (If instead m < x we can do the same, since also x < y).

    cases 
        : {x y : ℕ}
        → (Tri (x < y) (x ≡ y) (x > y))
        → ExRel hH x y
        → Path (R relates_to_) (Eq E) x y
    cases {x} (tri≈ _ refl _) _ = empty x
    cases {x} {y} (tri< x<y _ _) = to-< x<y (E y) refl
    cases {x} {y} (tri> _ _ y<x) xhHy = 
        path-sym (R relates_to_) (Eq E) 
        $ to-< {y} {x} y<x (E x) refl
            (relates-to-sym (exence-to-rel hH) {x} {y} xhHy)


    to : (x y : ℕ) 
        → ExRel hH x y
        → Path (R relates_to_) (Eq E) x y
    to x y = cases (<-cmp x y)
    from 
        : (x y : ℕ) 
        → Path (R relates_to_) (Eq E) x y
        → ExRel hH x y
    from x y p = ?

eqfil-closure-char-exence
    : (E : EqFilter)
    → (R : EqRel)
    → ClosureExBiimpl E R
eqfil-closure-char-exence E R x y = (to x y , from x y)
    where
        open EqfilClosureCharExenceImpl E R

--------------------------------------------------------------------------------
-- Main theorem stated in terms of EqRel
--------------------------------------------------------------------------------

            
-- Statement (final type) of the next theorem:
ClosureBiimpl
    : (E : EqFilter)
    → (R : EqRel)
    → Set
ClosureBiimpl E R = 
      (x y : ℕ)
    → (S relates x to y) 
      ↔
      (Path (R relates_to_) (Eq E) x y )
    where
        F : Filter
        F = EqFilter→Filter E
        C : IsClosable F
        C = EqFilter-IsClosable E
        -- S is the E-closure of R.
        S : EqRel
        S = rel (C R)

eqfilter-closure-characterisation
    : (E : EqFilter)
    → (R : EqRel)
    → ClosureBiimpl E R
eqfilter-closure-characterisation E R x y = 
    ↔-trans (closure-exence-to-eqrel E R x y) 
            (eqfil-closure-char-exence E R x y)
