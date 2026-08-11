-- Module      : Eser.Filters.Congruence
-- Description : Initial sketch how to implement 'is-a-congruence' as a Filter.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------

open import Data.Nat
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.Bool.Properties using (T-≡)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Relation.Nullary
open import Relation.Binary.Definitions using (Decidable ; DecidableEquality)
open import Data.Product
open import Data.Sum
open import Function using (_∘_ ; _$_ ; id)
open import Data.Maybe
open import Data.Maybe.Properties using (just-injective)

open import Data.Nat.Properties using (
    ≤-refl 
    ; ≤-trans 
    ; <-trans
    ; n≤1+n 
    ; ≡⇒≡ᵇ
    ; <-irrelevant
    ; n<1+n
    ; n≮0
    ; <-≤-trans
    ; ≤-<-trans
    ; m≤n⇒m<n∨m≡n
    )

open import Eser.EqRel.Definitions using (NFFun ; DecEquiv)
open import Eser.EqRel.Conversions using (RelToFun ; FunToRel)
open import Eser.Aux using (_↔_ ; _≈_ ; doubleSubst)
open import Eser.Logic using 
    (true≢false 
    ; ≡→≡ᵇ 
    ; ≡ᵇ→≡ 
    ; decEqReflection
    ; decEqCoReflection
    ; is-false-to-not-true
    )

open import Eser.Filters.Base
open import Eser.Filters.Properties
open import Eser.Filters.Resurface
open import Eser.Filters.PointwiseProperties
open import Eser.Filters.Conversions.NFFunToExence

module Eser.Filters.Congruence where

--------------------------------------------------------------------------------
-- 𝐂𝐎𝐍𝐆𝐑𝐔𝐄𝐍𝐂𝐄
-- This story is about implementing the 'is-a-congruence' predicate
-- for relations over term algebras over signatures.
-- The low-level definition of 'congruence' depends on the operations in
-- the signature, but it is unpractical to reimplement congruence 
-- for every signature.
--
-- So instead we define a generalisation of 'congruence' for any 'ReplaceStruct',
-- which are abstractions capturing only the minimal features of term algebras
-- needed to define congruence.
-- ReplaceStructs are enumerable types together with an
-- 'is-argument-of'-relation denoted as _⊂_,
-- and a replacement operation allowing to swap 'arguments'.
-- We only impose the minimal set of axioms needed to define
-- the generalisation of 'congruence', which we call 'ReplaceRespecting'.
-- Consequently, not all ReplacementStructs correspond to term algebras;
-- for example, we do not require that replacing an 
-- argument in a term with the same argument
-- leaves the term unchanged, nor that changing an argument x in a term t by x'
-- gives a term actually containing x' as argument.
-- However, when specialising to ReplaceStructs that do correspond to actual
-- term algebras, one does recover the traditional notion of congruence.
--
-- We only consider enumerable term algebras T, 
-- so w.l.o.g. we omit the bijection T ≃ ℕ and just work directly on ℕ.
--
-- Concretely, we will do the following:
-- 𝟏. Define ReplaceStructs.
-- 𝟐. Define two notions of ReplaceRespecting (parametrised by a ReplaceStruct).
--   Recall that decidable equivalence relations correspond
--   to normalisation functions ℕ → ℕ, which correspond to extension-sequences
--   (Exences). We can define predicates globally on equivalence relations,
--   or locally as Filters that constrain choices for the equivalence class
--   of n when extending the domain a restricted 
--   equivalence relation from {0, ..., n-1} to {0, ..., n}.
--   The notions are:
-- 𝟐.𝟏. A global notion on equivalence relations ℕ → ℕ → Bool.
-- 𝟐.𝟐. A local notion implemented as a Filter.
-- 𝟑. We prove that the global notion holds if and only if the local does.
--
-- Thereafter we will demonstrate this terse generalisation of congruence
-- 'works as intended' in practial contexts,
-- by specialising it to our implementation of signatures and term algebras
-- (from the modules in `Eser.Signature`, using the `Signatures` and
-- `ClosedTerms' of the `Eser` library):
-- 𝟒. Show that the closed terms over any Signature from a ReplaceStruct.
-- 𝟓. Define the traditional notion of 'congruence' (as a predicate
--  on relations).
-- 𝟔. Show that a relation satisfies this notion of congruence
--  if and only if it satisfies the (global notion) of 'ReplaceRespecting'.
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 𝟏. Replacement Structures
--------------------------------------------------------------------------------
-- Terse encoding of an enumerable type A with a 'is-argument-of'
-- relation _⊂_. We omit the bijection A ≃ ℕ and work on ℕ directly.
-- Arguments must be smaller in the enumertion than the term containing them.
-- There is a `replace` operation such that `replace y x x'`
-- represents the term `y` with argument `x` substituted by `x'`.
-- We abstract from most implementation details of `replace`,
-- and do not even distinguish between replacing a 
-- single or all occurrences of `x`.
-- Replacing an argument by a smaller one must result
-- in a term that is overall smaller.
--
-- Implementation note
-- I first used the following fields:
--      _⊂_ : ℕ → ℕ → Set
--      ⊂-dec : Decidable _⊂_
-- but then a `ReplaceStruct` becomes a Set₁, and I feared this may become an
-- annoyance further down the road.

record ReplaceStruct : Set where
    field
        _is-arg-of_ : ℕ → ℕ → Bool
        ⊂-resp-< : (y x : ℕ) → x is-arg-of y ≡ true → x < y
        replace : ℕ → ℕ → ℕ → ℕ
        replace-< 
            : (y x x' : ℕ) 
            → (x is-arg-of y ≡ true) 
            → (x' < x) 
            → (replace y x x' < y)
open ReplaceStruct


--------------------------------------------------------------------------------
-- 𝟐. Predicate 'ReplaceResp'
--------------------------------------------------------------------------------
module ReplaceResp (T : ReplaceStruct) where
    _⊂_ : ℕ → ℕ → Set
    _⊂_ n m = (_is-arg-of_ T) n m ≡ true

    _⊂?_ : (n m : ℕ) → Dec (n ⊂ m)
    n ⊂? m = ⊂?-cases (_is-arg-of_ T n m) refl
        where
            ⊂?-cases : (b : Bool) → (_is-arg-of_ T n m ≡ b) → Dec (n ⊂ m)
            ⊂?-cases true p = true because ofʸ p
            ⊂?-cases false p = false because ofⁿ 
                (is-false-to-not-true ((T is-arg-of n) m) p)


    ----------------------------------------------------------------------------
    -- 𝟐.𝟏. Global version
    ----------------------------------------------------------------------------
    -- A relation is 'Replacement Respecting'
    -- if replacing an argument x of y by a related argument x'
    -- results in a term y' that is related to y.
    module _ (R' : DecEquiv) where
        R = proj₁ R'
        ReplaceRespGlobal : Set
        ReplaceRespGlobal 
            = (y x x' : ℕ)
            → x ⊂ y
            → x' < x
            → R x x' ≡ true
            → R y (replace T y x x') ≡ true
        -- Remark: the `x' < x' premise is, intuitively, unnecessary.
        -- But it makes proving the correspondence to the local view
        -- much easier.
        -- For well-behaved `replace` functions it seems that this
        -- version of `ReplaceRespGlobal` implies the variant
        -- without the `x' < x` premise anyway (we don't prove this).

    ----------------------------------------------------------------------------
    -- 𝟐.𝟐. Local version
    ----------------------------------------------------------------------------

    -- An NFRestr n encodes an equivalence relation restricted
    -- to domain {0, ..., n-1}. So on this domain we can use it as a relation.
    -- Implementation note: this is not in `Eser.Filters.Base`
    -- nor in `Eser.Filter.Properties` because it depends
    -- on `Eser.Filter.Resurface`, which in turn depends
    -- on Base and Properties.
    NFRestrRel 
        : {n : ℕ}
        → (r : NFRestr n)
        → {x x' : ℕ}
        → x < n
        → x' < n
        → Bool
    NFRestrRel {n} r x<n x'<n = does (resurface r x<n ≡? resurface r x'<n)

    AreRelated : {n : ℕ} → (r : NFRestr n) → ℕ → ℕ → Set
    AreRelated {n} r x x' = (p : x < n) → (q : x' < n) → NFRestrRel r p q ≡ true

    areRelated? 
        : {y : ℕ} 
        → (r : NFRestr y) 
        → (x x' : ℕ) 
        → (x < y) 
        → (x' < y) 
        → Dec (AreRelated r x x')
    areRelated? {y} r x x' x<y x'<y with (resurface r x<y ≡? resurface r x'<y)
    ... | yes eq = yes (λ (a : x < y) (b : x' < y) → 
        let x<y≡a : x<y ≡ a 
            x<y≡a = <-irrelevant x<y a
        in
        let x'<y≡b : x'<y ≡ b 
            x'<y≡b = <-irrelevant x'<y b
        in
        doubleSubst (λ a b 
            → does (resurface r a ≡? resurface r b) ≡ true) x<y≡a x'<y≡b 
            $ decEqCoReflection _≡?_ (resurface r x<y) (resurface r x'<y) eq
        )
    ... | no  ¬eq = no (λ q → ¬eq 
        (decEqReflection _≡?_ (resurface r x<y) (resurface r x'<y) 
         $ q x<y x'<y))

    -- Check if the normal form of a number is equal to itself.
    IsNormal
        : {x y : ℕ}
        → (r : NFRestr y)
        → x < y
        → Set
    IsNormal {x} {y} r x<y = ¬ (Σ[ x' ∈ ℕ ] (x' < x) × (AreRelated r x x'))

    isNormal?
        : {x y : ℕ}
        → (r : NFRestr y)
        → (x<y : x < y)
        → IsNormal r x<y ⊎ Σ[ x' ∈ ℕ ] (x' < x) × AreRelated r x x'
    isNormal? {x} {y} r x<y = isNormal?-rec x ≤-refl
        where
            OutType : ℕ → Set
            OutType w = 
                  ¬ (Σ[ x' ∈ ℕ ] (x' < w) × AreRelated r x x') 
                  ⊎ 
                  Σ[ x' ∈ ℕ ] (x' < x) × AreRelated r x x'
            isNormal?-rec
                : (w : ℕ)
                → (w ≤ x)
                → OutType w
            isNormal?-rec 0 0≤x = inj₁ g
                where
                    0<y : 0 < y
                    0<y = ≤-<-trans 0≤x x<y

                    g : ¬ (Σ[ x' ∈ ℕ ] (x' < 0) × AreRelated r x x') 
                    g (x' , x'<0 , xR0) = ⊥-elim $ n≮0 x'<0

            isNormal?-rec w@(suc w') w≤x = 
                cases (isNormal?-rec w' (≤-trans (n≤1+n w') w≤x)) 
                      (areRelated? r x w' x<y (<-trans w'<x x<y) )
                where
                    w'<x : w' < x
                    w'<x = <-≤-trans (n<1+n w') w≤x
                    cases 
                        : (p : OutType w')
                        → (Dec (AreRelated r x w'))
                        → OutType w
                    cases (inj₂ p) wR?x = inj₂ p
                    cases (inj₁ _) (yes w'Rx) = inj₂ (w' , w'<x , w'Rx)
                    cases (inj₁ p) (no ¬w'Rx) = inj₁ g
                        where
                            g : ¬ (Σ[ x' ∈ ℕ ] (x' < w) × AreRelated r x x') 
                            g (x' , x'<w , x'Rx) with (m≤n⇒m<n∨m≡n (s≤s⁻¹ x'<w))
                            ... | inj₁ (x'<w') = p (x' , x'<w' , x'Rx)
                            ... | inj₂ refl  = ¬w'Rx x'Rx
    
    -- Predicate that no argument of y is related (according to r)
    -- to a smaller term.
    AllArgsNormal
        : {y : ℕ}
        → (r : NFRestr y)
        → Set
    AllArgsNormal {y} r
        = (x : ℕ) 
        → (x ⊂ y)
        → ¬ (Σ[ x' ∈ ℕ ] 
                (x' < x)
                × 
                (AreRelated r x x')
            )
    -- Note: p and q are proof-irrelevant, and are already implied
    -- by x ⊂ y and (via transitivity) x' < x.
    -- However, giving them as arguments is more convenient than
    -- fixing defaults and having to use `subst`.
    
    -- Proof-relevant predicate that y has an argument x
    -- that is (according to r) related to x' with x' < x.
    NonNormalArg
        : {y : ℕ}
        → (r : NFRestr y)
        → Set
    NonNormalArg {y} r =
        Σ[ x ∈ ℕ ] Σ[ x' ∈ ℕ ] (x ⊂ y) × (x' < x) × (AreRelated r x x')

    AllSmallerNormal : {y : ℕ} → (r : NFRestr y) → ℕ → Set
    AllSmallerNormal {y} r x = 
        ((z : ℕ) 
                → (z ≤ x) 
                → (z⊂y : z ⊂ y) 
                → IsNormal r (⊂-resp-< T y z z⊂y) 
          )
    
    -- Auxiliary function of allArgsNormal? below.
    allArgsNormal?Rec
        : (x y : ℕ)
        → (r : NFRestr y)
        → (x < y)
        → AllSmallerNormal r x ⊎ NonNormalArg r
    allArgsNormal?Rec 0 y r x<y = inj₁ p
        where
            p   : (z : ℕ) 
                → z ≤ 0 
                → (z⊂y : z ⊂ y) 
                → IsNormal r (⊂-resp-< T y z z⊂y)
            p z z≤0 z⊂y (x' , x'<z , zRx') = ⊥-elim $ n≮0 (<-≤-trans x'<z z≤0)
    allArgsNormal?Rec x@(suc x') y r x<y = allArgsNormal?Rec-cases 
       (allArgsNormal?Rec x' y r x'<y) refl (x ⊂? y)
        where
            x'<y : x' < y
            x'<y = <-trans (n<1+n x') x<y
            allArgsNormal?Rec-cases
                : (p : AllSmallerNormal r x' ⊎ NonNormalArg r)
                → (p ≡ allArgsNormal?Rec x' y r x'<y)
                → (Dec (x ⊂ y))
                → AllSmallerNormal r x ⊎ NonNormalArg r
            allArgsNormal?Rec-cases-x⊂y 
                : (p : AllSmallerNormal r x')
                → x ⊂ y
                → AllSmallerNormal r x ⊎ NonNormalArg r

            allArgsNormal?Rec-cases (inj₂ nonNormal) p-eq _ = inj₂ nonNormal
            allArgsNormal?Rec-cases (inj₁ p') p-eq (yes x⊂y) = 
                allArgsNormal?Rec-cases-x⊂y p' x⊂y
            allArgsNormal?Rec-cases (inj₁ p') p-eq (no x⊄y) = inj₁ g
                where
                    g : AllSmallerNormal r x
                    g z z≤x z⊂y with (m≤n⇒m<n∨m≡n z≤x)
                    ... | inj₂ (z≡x) = ⊥-elim $ x⊄y (subst (_⊂ y) z≡x z⊂y )
                    ... | inj₁ (z<x) = k
                        where
                            z<y : z < y
                            z<y = ⊂-resp-< T y z z⊂y

                            k : IsNormal r z<y
                            k = p' z (s≤s⁻¹ z<x) z⊂y
            allArgsNormal?Rec-cases-x⊂y allSmallerNorm x⊂y with isNormal? r x<y
            ... | inj₁ isNormal = inj₁ g
                where
                    g : AllSmallerNormal r x
                    g z z≤x z⊂y with (m≤n⇒m<n∨m≡n z≤x)
                    ... | inj₂ (refl) = isNormal
                    ... | inj₁ (z<x) = allSmallerNorm z (s≤s⁻¹ z<x) z⊂y
            ... | inj₂ (x'' , x''<x , xRx'')  
                = inj₂ (x , x'' , x⊂y , x''<x , xRx'')

    -- Test if some argument of y has a normal form (accoding to r)
    -- not equal to itself.
    -- Implementation: just brute force check all x < y by induction.
    allArgsNormal?
        : {y : ℕ}
        → (r : NFRestr y)
        → AllArgsNormal r ⊎ NonNormalArg r
    allArgsNormal? {0} r = inj₁ ans
        where
            ans : (x : ℕ) → (x ⊂ 0)
                → ¬ (Σ[ x' ∈ ℕ ] 
                     (x' < x)
                     ×
                     (AreRelated r x x')
                    )
            ans x x⊂0 = ⊥-elim $ n≮0 (⊂-resp-< T 0 x x⊂0)
    allArgsNormal? y@{suc y'} r with allArgsNormal?Rec y' (suc y') r (n<1+n y')
    ... | inj₁ allSmallerNormal = inj₁ ans
        where
            ans : (x : ℕ) → (x⊂y : x ⊂ y) → IsNormal r (⊂-resp-< T y x x⊂y)
            ans x x⊂y (x' , x'<x , xRx') = 
                allSmallerNormal x (s≤s⁻¹ $ ⊂-resp-< T y x x⊂y) 
                                 x⊂y (x' , x'<x , xRx')
    ... | inj₂ p = inj₂ p


    -- Given evidence of a non-normal argument, we know the output of
    -- `allArgsNormal?`.
    lemma-allArgsNormal?-NonNormal
        : {y : ℕ}
        → (r : NFRestr y)
        → {x x' : ℕ}
        → (x⊂y : x ⊂ y)
        → (x'<x : x' < x)
        → (xRx' : AreRelated r x x')
        → allArgsNormal? r ≡ inj₂ (x , x' , x⊂y , x'<x , xRx')
    lemma-allArgsNormal?-NonNormal = ?
        

    -- 𝟐.𝟐. Local version.
    -- When needing to filter out the allowed equivalence classes for `y`,
    -- it checks whether `y` contains an argument x 'not in normal form',
    -- which in this abstract context is defined as 'related to a smaller term
    -- x' '.
    -- If it does, then the only allowed equivalence class
    -- is the class of `replace y x x'`; since `replace y x x' < y` this choice
    -- is indeed available.
    -- Otherwise the filter gives free choices.
    ReplaceRespLocal : Filter
    ReplaceRespLocal-cases 
        : {y : ℕ}
        → (r : NFRestr y)
        → (c : Choices r)
        → AllArgsNormal r ⊎ NonNormalArg r
        → Bool
    -- All args are normal, no congruence constraints; free choice!
    ReplaceRespLocal-cases {y} r _ (inj₁ _) = true 
    -- Some argument of y can be 'normalised'. The equivalence class
    -- of y must equal the equivalence class of 
    -- y-but-with-this-argument-normalised.
    ReplaceRespLocal-cases {y} r c (inj₂ (x , x' , x⊂y , x'<x , x'∼x)) =
        does (c ≡? y'-nf)
        where
            y' : ℕ
            y' = replace T y x x'
            y'<y : y' < y
            y'<y = replace-< T y x x' x⊂y x'<x
            -- Resurface the normal form of y' as a choice of normal form for y.
            y'-nf : Choices r
            y'-nf = earlier-new $ resurface r y'<y

    ReplaceRespLocal {y} r c = ReplaceRespLocal-cases {y} r c (allArgsNormal? r)
    
    -- If known that `y` has a non-normal argument,
    -- then we know the output of ReplaceRespLocal:
    -- the only allowed choice for the nf of y is
    -- the nf of replace y x x'.
    lemma-ReplaceRespLocal-NonNormalArg-Exence
        : {y x x' : ℕ}
        → (h : (n : ℕ) → NFRestr n)
        → (H : (n : ℕ) → h n ⋖ h (suc n))
        → x ⊂ y
        → x' < x
        → (p : (replace T y x x') < y)
        → AreRelated (h y) x x'
        → Exence-sats ReplaceRespLocal (h , H)
        → getChoiceFromExence (h , H) y ≡ (earlier-new $ resurface (h y) p)
    lemma-ReplaceRespLocal-NonNormalArg-Exence {y} {x} {x'} h H x⊂y x'<x y'<y 
                                               xRx' LocSat 
                                               = decEqReflection _≡?_ LHS RHS K'
        where
            LHS : Choices (h y)
            LHS = getChoiceFromExence (h , H) y

            RHS : Choices (h y)
            RHS = earlier-new $ resurface (h y) y'<y

            F : Filter
            F = ReplaceRespLocal

            K : F (h y) LHS ≡ true
            K = LocSat y

            y' : ℕ
            y' = replace T y x x'

            y'<y-alt : y' < y
            y'<y-alt = replace-< T y x x' x⊂y x'<x

            
            y'<y-alt≡y'<y : y'<y-alt ≡ y'<y
            y'<y-alt≡y'<y = <-irrelevant y'<y-alt y'<y

            -- Compute definition of F, after forcing the output of
            -- the call to `allArgsNormal?`.
            K' : does (LHS ≡? RHS) ≡ true
            K' = sym $
                begin 
                    true 
                ≡⟨ sym K ⟩
                    F (h y) LHS
                ≡⟨⟩
                    ReplaceRespLocal-cases (h y) LHS (allArgsNormal? (h y))
                ≡⟨ cong (ReplaceRespLocal-cases (h y) LHS) 
                   $ lemma-allArgsNormal?-NonNormal (h y) x⊂y x'<x xRx' ⟩ 
                    ReplaceRespLocal-cases (h y) LHS 
                        (inj₂ (x , x' , x⊂y , x'<x , xRx'))
                ≡⟨⟩ -- Definition ReplaceRespLocal-cases.
                    does (LHS ≡? (earlier-new $ resurface (h y) y'<y-alt))
                    -- Now substitute the proof-irrelevant proof that
                    -- y' < y by the one given.
                ≡⟨ cong (λ p → does (LHS ≡? (earlier-new $ resurface (h y) p)))
                        y'<y-alt≡y'<y ⟩
                    does (LHS ≡? RHS)
                ∎
    -- Variant of the above lemma in special case where the Exence
    -- is a restrict+-ed normalisation function f.
    -- It carries the result back from an equality on used extension choices
    -- in restrictions of f to an equality on inputs to f.
    -- Implementation note: we don't take an argument z
    -- of type `z : NonNormalArg {y} r` because the output type depends on
    -- the data within z, namely x and x'.
    lemma-ReplaceRespLocal-NonNormalArg-NFFun
        : {y x x' : ℕ}
        → x ⊂ y
        → x' < x
        → (f' : NFFun)
        → AreRelated (restrict f' y) x x'
        → NFFun-sats ReplaceRespLocal f'
        → (proj₁ f' y) ≡ (proj₁ f' (replace T y x x'))
    lemma-ReplaceRespLocal-NonNormalArg-NFFun {y} {x} {x'} x⊂y x'<x 
                                        f'@(f , f-leq , f-fix) xRx' LocSat =
        begin 
            f y    
        ≡⟨⟩
            proj₁ f' y
        ≡⟨ sym $ theo-combine∘restrict+ f' y ⟩
            (proj₁ ∘ combine ∘ restrict+) f' y
        ≡⟨⟩ -- Unfold definition of `combine`:
            (choiceToℕ ∘ (getChoiceFromExence $ restrict+ f')) y
        -- #TODO: some lemma with r := restrict f' y and E = restrict+ f'
        ≡⟨ cong choiceToℕ forcedChoice ⟩
            choiceToℕ (earlier-new $ resurface (restrict f' y) y'<y)
        ≡⟨⟩ -- Maybe we don't need this step.
            NFSToℕ (resurface (restrict f' y) y'<y)
        ≡⟨ lemma-resurface-getChoice h H y'<y ⟩
            (choiceToℕ ∘ (getChoiceFromExence $ restrict+ f')) y'
        ≡⟨⟩ -- Fold definition `combine`.
            (proj₁ ∘ combine ∘ restrict+) f' y'
        ≡⟨ theo-combine∘restrict+ f' y' ⟩
            proj₁ f' y'
        ≡⟨⟩
            f y' 
        ∎
        where
            y' : ℕ
            y' = replace T y x x'

            y'<y : y' < y
            y'<y = replace-< T y x x' x⊂y x'<x

            h = proj₁ $ restrict+ f'
            H = proj₂ $ restrict+ f'

            forcedChoice : getChoiceFromExence (restrict+ f') y 
                           ≡ 
                           (earlier-new $ resurface (restrict f' y) y'<y)
            forcedChoice = lemma-ReplaceRespLocal-NonNormalArg-Exence
                h H x⊂y x'<x y'<y xRx' LocSat
        
        
    ----------------------------------------------------------------------------
    -- 𝟑. Correspondence Global and Local definition
    ----------------------------------------------------------------------------

    ----------------------------------------------------------------------------
    -- Auxiliary result: FunToRel and AreRelated∘restrict are the same relation.
    ----------------------------------------------------------------------------
    -- This is relevant because ReplaceRespGlobal uses FunToRel
    -- and ReplaceRespLocal uses AreRelated∘restrict.
    -- So the proof of the theorem ReplaceRespGlobal <-> ReplaceRespLocal
    -- needs to use  FunToRel <-> AreRelated∘restrict.
    

    lemma-FunToRel-AreRelated
        : (f' : NFFun)
        → (x x' : ℕ)
        → proj₁ (FunToRel f') x x' ≡ true
        → (y : ℕ)
        → AreRelated (restrict f' y) x x'
    lemma-FunToRel-AreRelated f'@(f , f-leq , f-fix) x x' xRx' y x<y x'<y 
        = NFS-DecEq
        where
            -- From xRx' and definition of FunToRel f' we get:
            fx≡f'x : f x ≡ f x'
            fx≡f'x = ≡ᵇ→≡ (f x) (f x') xRx'

            NFS-as-ℕ-Eq :
                NFSToℕ (resurface (restrict f' y) x<y)
                ≡ 
                NFSToℕ (resurface (restrict f' y) x'<y)
            NFS-as-ℕ-Eq = doubleSubst {ℕ} {ℕ} _≡_ p q fx≡f'x
                where
                    p = sym $ resurf-restrict-to-fun-output f' y x x<y
                    q = sym $ resurf-restrict-to-fun-output f' y x' x'<y

            c = resurface (restrict f' y) x<y
            c' = resurface (restrict f' y) x'<y

            NFS-Eq : 
                (resurface (restrict f' y) x<y)
                ≡ 
                (resurface (restrict f' y) x'<y)
            NFS-Eq = NFSToℕ-injective c c' NFS-as-ℕ-Eq

            NFS-DecEq :
                does (
                    (resurface (restrict f' y) x<y)
                    ≡? 
                    (resurface (restrict f' y) x'<y)
                ) ≡ true
            NFS-DecEq = decEqCoReflection _≡?_ c c' NFS-Eq

    lemma-AreRelated-FunToRel
        : (f' : NFFun)
        → (x x' : ℕ)
        → (y : ℕ)
        → x < y
        → x' < y
        → AreRelated (restrict f' y) x x'
        → proj₁ (FunToRel f') x x' ≡ true
    lemma-AreRelated-FunToRel f'@(f , f-leq , f-fix) x x' y x<y x'<y xRx' = ans
        where
            r : NFRestr y
            r = restrict f' y

            resurf-eq : resurface r x<y ≡ resurface r x'<y
            resurf-eq = decEqReflection _≡?_ 
                (resurface r x<y) (resurface r x'<y) $ xRx' x<y x'<y

            ans : (f x ≡ᵇ f x') ≡ true
            ans = ≡→≡ᵇ (f x) (f x') $
                begin 
                    f x
                ≡⟨ sym $ resurf-restrict-to-fun-output f' y x x<y ⟩
                    NFSToℕ (resurface r x<y)
                ≡⟨ cong NFSToℕ resurf-eq ⟩
                    NFSToℕ (resurface r x'<y)
                ≡⟨ resurf-restrict-to-fun-output f' y x' x'<y ⟩
                    f x'
                ∎
                

    ----------------------------------------------------------------------------
    -- Main theorems
    ----------------------------------------------------------------------------

    -- Implementation note: we could also have given a `R' : DecEquiv`
    -- and use RelToFun instead. 
    theo-ReplaceResp-left
        : (f' : NFFun)
        → ReplaceRespGlobal (FunToRel f') → NFFun-sats ReplaceRespLocal f'
    theo-ReplaceResp-right
        : (f' : NFFun)
        → NFFun-sats ReplaceRespLocal f' → ReplaceRespGlobal (FunToRel f')
    theo-ReplaceResp-correspondence
        : (f' : NFFun)
        → ReplaceRespGlobal (FunToRel f') ↔ NFFun-sats ReplaceRespLocal f'
    theo-ReplaceResp-correspondence f' = (theo-ReplaceResp-left f'
                                         , theo-ReplaceResp-right f')

    theo-ReplaceResp-left-cases
        : (f' : NFFun)
        → (y : ℕ)
        → (p : AllArgsNormal (restrict f' y) ⊎ NonNormalArg (restrict f' y))
        → p ≡ allArgsNormal? (restrict f' y)
        → ReplaceRespGlobal (FunToRel f') 
        → ReplaceRespLocal Allows (getChoiceFromExence (restrict+ f') y) 
                           In (restrict f' y)

    theo-ReplaceResp-left f' G y 
        = theo-ReplaceResp-left-cases f' y (allArgsNormal? (restrict f' y)) refl G

    theo-ReplaceResp-left-cases f' y (inj₁ normal) p≡allArgsNormal? G =
        -- This case is easy: all arguments to y are in normal form,
        -- so ResplaceRespLocal just gives free choice;
        -- in particular including the choice c.
        let r = (restrict f' y) in
        let c = (getChoiceFromExence (restrict+ f') y) in
        begin 
            ReplaceRespLocal r c
        ≡⟨⟩ -- Definition ReplaceRespLocal
            ReplaceRespLocal-cases r c (allArgsNormal? r)
        ≡⟨ cong (ReplaceRespLocal-cases r c) (sym p≡allArgsNormal?) ⟩
            ReplaceRespLocal-cases r c (inj₁ normal)
        ≡⟨⟩
            true
        ∎
        
    theo-ReplaceResp-left-cases f'@(f , f-leq , f-fix) y 
                                (inj₂ p@(x , x' , x⊂y , x'<x , xRx')) 
                                p≡allArgsNormal? G =
        begin 
            ReplaceRespLocal r c
        ≡⟨⟩
            ReplaceRespLocal-cases r c (allArgsNormal? r)
        ≡⟨ cong (ReplaceRespLocal-cases r c) (sym p≡allArgsNormal?) ⟩
            ReplaceRespLocal-cases r c (inj₂ p)
        ≡⟨⟩
            does (c ≡? y'-nf)
        ≡⟨ decEqCoReflection _≡?_ c y'-nf choice-eq ⟩
            true
        ∎
        where
            r : NFRestr y
            r = restrict f' y
            c : Choices r
            c = getChoiceFromExence (restrict+ f') y
            y' : ℕ
            y' = replace T y x x'
            y'<y : y' < y
            y'<y = replace-< T y x x' x⊂y x'<x
            y'-nf : Choices r
            y'-nf = earlier-new $ resurface r y'<y


            x<y : x < y
            x<y = ⊂-resp-< T y x x⊂y
            x'<y : x' < y
            x'<y = <-trans x'<x x<y

            q' : f x ≡ f x'
            q' = ≡ᵇ→≡ (f x) (f x') 
                       $ lemma-AreRelated-FunToRel f' x x' y x<y x'<y xRx'
                
            fy≡fy' : f y ≡ f y'
            fy≡fy' = ≡ᵇ→≡ (f y) (f y') 
                $ G y x x' x⊂y x'<x (≡→≡ᵇ (f x) (f x') q')

            z : ℕ
            z = suc y
            y<z : y < z
            y<z = n<1+n y
            y'<z : y' < z
            y'<z = <-trans y'<y y<z

            r' : NFRestr z
            r' = restrict f' z
                
            q'' : NFSToℕ(resurface r' y<z) ≡ NFSToℕ(resurface r y'<y)
            q'' = 
                begin 
                    NFSToℕ(resurface r' y<z)
                ≡⟨ resurf-restrict-to-fun-output f' z y y<z ⟩
                    f y
                ≡⟨ fy≡fy' ⟩
                    f y'
                ≡⟨ sym $ resurf-restrict-to-fun-output f' y y' y'<y ⟩
                    NFSToℕ(resurface r y'<y)
                ∎

            h = proj₁ $ restrict+ f'
            H = proj₂ $ restrict+ f'

            choice-eq : c ≡ y'-nf
            choice-eq = 
                choiceToℕ-injective c y'-nf $ 
                begin 
                  choiceToℕ c
                ≡⟨ sym $ lemma-resurface-getChoice h H y<z  ⟩
                  NFSToℕ (resurface r' y<z)
                ≡⟨ q'' ⟩
                  NFSToℕ (resurface r y'<y)
                ≡⟨⟩
                  choiceToℕ (earlier-new y'-nf)
                ∎
                

    -- Strategy of right-to-left direction: 
    -- pattern match on the Boolean `R y (replace T y x x')`
    -- where R ≗ proj₁ (FunToRel f'),
    -- i.e., (unfolding R), pattern match on `f y ≡ᵇ f (replace T y x x')`.
    -- The `true` case is trivial.
    -- The `false` case leads to a contradiction, since f satisfies
    -- the ReplaceRespLocal filter; not all of y' arguments are normal
    -- (x is a counterexample), so the filter only allows the choice
    -- `replace T y x x'` for f y.
    theo-ReplaceResp-right-cases
        : (f' : NFFun)
        → NFFun-sats ReplaceRespLocal f' 
        → (y x x' : ℕ)
        → x ⊂ y
        → x' < x
        → (proj₁ $ FunToRel f') x x' ≡ true
        → (b : Bool)
        → (proj₁ $ FunToRel f') y (replace T y x x') ≡ b
        → b ≡ true
    theo-ReplaceResp-right f' LocSat y x x' x⊂y x'<x xRx' = 
        theo-ReplaceResp-right-cases f' LocSat y x x' x⊂y x'<x xRx' b refl
            where
                b : Bool
                b = (proj₁ $ FunToRel f') y (replace T y x x')

    theo-ReplaceResp-right-cases f' LocSat y x x' x⊂y x'<x xRx' true p = refl
    theo-ReplaceResp-right-cases f' LocSat y x x' x⊂y x'<x xRx' false p = 
        ⊥-elim contra
        where

            xRx'-alt : AreRelated (restrict f' y) x x'
            xRx'-alt = lemma-FunToRel-AreRelated f' x x' xRx' y


            NonNormalArg-y : NonNormalArg (restrict f' y)
            NonNormalArg-y = (x , x' , x⊂y , x'<x , xRx'-alt)

            fy-as-choice : Choices (restrict f' y)
            fy-as-choice = getChoiceFromExence (restrict+ f') y

            y' : ℕ
            y' = replace T y x x'

            f : ℕ → ℕ
            f = proj₁ f'

            -- Unfold the definition of `FunToRel f'` in p to obtain:
            p' : (f y ≡ᵇ f y') ≡ false
            p' = p

            fy≢fy' : f y ≢ f y'
            fy≢fy' fy≡fy' = true≢false $ trans (sym $ ≡→≡ᵇ (f y) (f y') fy≡fy') p

            fy≡fy' : f y ≡ f y'
            fy≡fy' = lemma-ReplaceRespLocal-NonNormalArg-NFFun x⊂y x'<x f' 
                                                               xRx'-alt LocSat


            -- By definition of ReplaceRespLocal-cases,
            -- the following is only possible if fy-as-choice
            -- equals `earlier-new $ resurface r y'<y`.
            -- We know this is not the case since `p` proves that f y ≢ f y'
            -- (where y'  ≔ replace y x x').
            satAty : ReplaceRespLocal {y} (restrict f' y) fy-as-choice ≡ true
            satAty = LocSat y

            contra : ⊥
            contra = fy≢fy' fy≡fy'

--------------------------------------------------------------------------------
-- 𝟒. Signatures give ReplaceStructs
--------------------------------------------------------------------------------
open import Eser.Signature.Definitions
open import Eser.Signature.MainTheorem
open import Eser.Card
open import Eser.Equivalences
open import Eser.Equivalences.Notation

module ForSignature {μ : ℕ∞} {ζ : ℕ∞} (S : Signature (suc∞ μ) (suc∞ ζ)) where
    -- Implementation note: we are using the version with weight annotations
    -- because this will make it much easier to prove how replacement of an
    -- argument by a smaller argument leads to a smaller term.
    C = ClosedTerms {suc∞ μ} {suc∞ ζ} S
    OT = OpenTerms {suc∞ μ} {suc∞ ζ} S

    -- Is-an-argument-of-relation.
    -- Not to be confused with the 'subterm' relation in Eser.Signature.Subterm.
    -- The latter relation is transitive and also relates
    -- t to `giveArg t a`, while t is not an argument.
    data _⋤_ : {n n' w w' : ℕ} → OT w n → OT w' n' → Set where
        here 
            : {n wₜ wₐ : ℕ} 
            → (t : OT wₜ (ℕ.suc n)) 
            → (a : OT wₐ 0) 
            → a ⋤ giveArg t a
        earlier 
            : {n wₜ wₐ wₐ' : ℕ} 
            → (t : OT wₜ (ℕ.suc n)) 
            → (a : OT wₐ 0) 
            → (a' : OT wₐ' 0) 
            → a ⋤ t
            → a ⋤ giveArg t a'

    -- Replacement of arguments defined on Open Terms.
    -- The enumeration bijection will allow to lift this from OT to ℕ.
    OT-replace 
        : {n wₜ wₐ wₐ' : ℕ} 
        → (t : OT wₜ n) 
        → (a : OT wₐ 0) 
        → (a' : OT wₐ' 0) 
        → a ⋤ t 
        --^ Implies wₜ > wₐ, so wₜ ∸ wₐ will be nonzero.
        --  Can be proven using `subterm-smaller-weight` in Signature.Subterm.
        → Σ[ w' ∈ ℕ ] Σ[ t' ∈ OT w' n ] (a' ⋤ t) × (w' ≡ (wₜ + wₐ') ∸ wₐ)
    OT-replace t a a' = ?

    𝕋 : Set
    𝕋 = AllTerms {suc∞ μ} {suc∞ ζ} S

    𝕋≃ℕ = infTermAlgEnum {μ} {ζ} S
    --open EquivShorthandsForEnumSet 𝕋≃ℕ
    φ : 𝕋 → ℕ
    φ = ≃-to 𝕋≃ℕ
    φ⁻¹ : ℕ → 𝕋
    φ⁻¹ = ≃-from 𝕋≃ℕ
    φ∘φ⁻¹≈id : (φ ∘ φ⁻¹) ≈ id
    φ∘φ⁻¹≈id = ≃-toFrom 𝕋≃ℕ
    φ⁻¹∘φ≈id : (φ⁻¹ ∘ φ) ≈ id
    φ⁻¹∘φ≈id = ≃-fromTo 𝕋≃ℕ

    -- #TODO: if `a` doesn't occur in t then return t unchanged.
    -- So add a case distinction!
    sig-replace : ℕ → ℕ → ℕ → ℕ
    sig-replace t a a' = 
        let (w' , t' , _) = OT-replace (proj₂ $ φ⁻¹ t) (proj₂ $ φ⁻¹ a) 
                                       (proj₂ $ φ⁻¹ a') ?
        in
        φ (w' , t')

    -- Extract underlying replacement structure from a Signature.
    toReplaceStruct : ReplaceStruct
    toReplaceStruct ._is-arg-of_ = {! !}
    toReplaceStruct .⊂-resp-< = {! !}
    toReplaceStruct .replace = {! !}
    toReplaceStruct .replace-< = {! !}

    ----------------------------------------------------------------------------
    -- 𝟓. Familiar definition of congruence
    ----------------------------------------------------------------------------
    -- Is-an-argument-of-relation, lifted to ℕ via the bijection φ : 𝕋 ≃ ℕ.
    _⋤ℕ_ : ℕ → ℕ → Set
    t ⋤ℕ a = (proj₂ $ φ⁻¹ t) ⋤ (proj₂ $ φ⁻¹ a)

    IsCongruence : DecEquiv → Set
    IsCongruence R'@(R , is-equiv-rel) 
        = (t : ℕ)                         --^ For all closed terms t ...
        → (a : ℕ) → (a ⋤ℕ t)              --^ ... and all arguments a of t
        → (a' : ℕ)                        --^ ... and all alternatives a'
        → R a a' ≡ true                   --^     that are related to a
        → R t (sig-replace t a a') ≡ true --^ t and t[a'/a] must be related.
            
    ----------------------------------------------------------------------------
    -- 𝟔. ReplaceResp specialises to IsCongruence for Signatures
    ----------------------------------------------------------------------------
    open ReplaceResp toReplaceStruct
    theo-ReplaceResp-is-IsCongr
        : (R : DecEquiv)
        → ReplaceRespGlobal R ↔ IsCongruence R
    theo-ReplaceResp-is-IsCongr R = ?
