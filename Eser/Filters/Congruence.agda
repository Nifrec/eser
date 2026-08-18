-- Module      : Eser.Filters.Congruence
-- Description : Initial sketch how to implement 'is-a-congruence' as a Filter.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------

open import Data.Nat
open import Data.Bool hiding (_<_ ; _≤_ ; _≟_ ; _≤?_ )
open import Data.Bool.Properties using (T-≡)
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Relation.Binary
open ≡-Reasoning
open import Relation.Nullary
open import Relation.Binary.Definitions using (Decidable ; DecidableEquality 
    ; tri< ; tri≈ ; tri>)
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
    ; n≮n
    ; ≰⇒>
    )

open import Eser.EqRel.Definitions using (NFFun ; DecEquiv)
open import Eser.EqRel.Conversions using (RelToFun ; FunToRel)
open import Eser.Aux using (_↔_ ; _≈_ ; doubleSubst ; irrel-×-closure ; uip
    ; restIsProofIrrel
    )
open import Eser.Logic using 
    (true≢false 
    ; ≡→≡ᵇ 
    ; ≡ᵇ→≡ 
    ; decEqReflection
    ; decEqCoReflection
    ; is-false-to-not-true
    ; not-true-to-is-false
    )
open import Eser.NatTriples

open import Eser.Filters.Base
open import Eser.Filters.Properties
open import Eser.Filters.Resurface
open import Eser.Filters.PointwiseProperties
open import Eser.Filters.Conversions.NFFunToExence
open import Eser.Filters.ReplaceStructs
open import Eser.Filters.NormalityInNFRestr

module Eser.Filters.Congruence where

--------------------------------------------------------------------------------
-- 𝐂𝐎𝐍𝐆𝐑𝐔𝐄𝐍𝐂𝐄
-- This story is about implementing the 'is-a-congruence' predicate
-- for relations over term algebras over signatures.
-- The low-level definition of 'congruence' depends on the operations in
-- the signature, but it is unpractical to reimplement congruence 
-- for every signature.
--
-- So instead we define 'ReplaceRespecting' as 
-- a generalisation of 'congruence' for any 'replacement structure'.
-- Replacement structres are abstractions capturing only the minimal features 
-- of term algebras needed to define congruence.
-- They are enumerable types together with an
-- 'is-argument-of'-relation denoted as _⊂_,
-- and a replacement operation allowing to swap 'arguments'.
-- We do not explicitly record the enumerable type itself,
-- but define everything for ℕ; this can easily be carried over via an
-- equivalence to A if A ≃ ℕ.
-- Replacement structures only have the minimal set of axioms needed to define
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
-- 𝟏. Define ReplaceStructs (see module Eser.Filters.ReplaceStructs).
-- 𝟐. Define two notions of 'ReplaceRespecting' 
--   (parametrised by a ReplaceStruct).
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
--   (see module Filters.ReplaceStruct.ForSignature).
-- 𝟓. Define the traditional notion of 'congruence' 
--   (as a predicate on relations).
--   (see module Filters.ReplaceStruct.ForSignature).
-- 𝟔. Show that a relation satisfies this notion of congruence
--   if and only if it satisfies the (global notion) of 'ReplaceRespecting'.
--   (see module Filters.Congruence.ForSignature).
--------------------------------------------------------------------------------

--------------------------------------------------------------------------------
-- 𝟐. Predicate 'ReplaceResp'
--------------------------------------------------------------------------------
module ReplaceResp (T : ReplaceStruct) where
    open ReplaceStructLemmas T
    open ReplaceStruct
    open NormalityForReplStruct T

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
    ReplaceRespLocal-cases {y} r c (inj₂ (x , x' , x⊂y  , x'<x , xRx')) =
        does (c ≡? y'-nf)
        where
            y' : ℕ
            y' = replace T y x x'
            y'<y : y' < y
            y'<y = replace-< T y x x' x⊂y x'<x
            -- Resurface the normal form of y' as a choice of normal form for y.
            y'-nf : Choices r
            y'-nf = earlier-new $ resurface r y'<y

    ReplaceRespLocal {y} r c = 
        ReplaceRespLocal-cases {y} r c (forgetMinimality $ allArgsNormal? r)
    
        
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
                
    -- If two elements have the same normal form in a NFRestr `s`
    -- then then also do have the same normal form in any restriction
    -- of `s`. More specifically, we use the definition `AreRelated`,
    -- which ensures they are still related even when not an element
    -- of the NFRestr 
    -- (i.e., when one of the two elements is at least as great as the
    -- index of the NFRestr).
    areRelated-in-restriction
        : {m n : ℕ}
        → (r : NFRestr m)
        → (s : NFRestr n)
        → r ⋖+ s
        → {x x' : ℕ}
        → x' < x
        → AreRelated s x x'
        → AreRelated r x x'
    areRelated-in-restriction {m} {n} r s r⋖+s {x} {x'} x'<x xSx' with m ≤? x
    ... | (yes m≤x) = ans
        where
            ans : AreRelated r x x'
            ans x<m = ⊥-elim $ n≮n m $ ≤-<-trans m≤x x<m
    ... | (no m≰x) = ans 
        where
            m<n : m < n
            m<n = lemma-⋖+-indices r⋖+s
            x<n : x < n
            x<n = <-trans (≰⇒> m≰x) m<n
            x'<n : x' < n
            x'<n = <-trans x'<x x<n
            eq : NFSToℕ (resurface s x<n) ≡ NFSToℕ (resurface s x'<n)
            eq = cong NFSToℕ $ decEqReflection _≡?_ (resurface s x<n) 
                                                    (resurface s x'<n) 
                             $ xSx' x<n x'<n

            ans : AreRelated r x x'
            ans x<m x'<m =
                decEqCoReflection _≡?_ (resurface r x<m) (resurface r x'<m)
                $ NFSToℕ-injective (resurface r x<m) (resurface r x'<m)
                $ just-injective
                $ begin 
                    (just $ NFSToℕ $ resurface r x<m)
                ≡⟨ resurface-correctness r x<m x<m ⟩
                    NFRestrToℕ (trim' r x<m)
                ≡⟨ cong NFRestrToℕ $ lemma-⋖+-trim'-equal r⋖+s x<m x<n ⟩
                    NFRestrToℕ (trim' s x<n)
                ≡⟨ sym $ resurface-correctness s x<n x<n ⟩
                    (just $ NFSToℕ $ resurface s x<n) 
                ≡⟨ cong just eq ⟩
                    (just $ NFSToℕ $ resurface s x'<n)  
                ≡⟨ resurface-correctness s x'<n x'<n ⟩
                    NFRestrToℕ (trim' s x'<n)
                ≡⟨ sym $ cong NFRestrToℕ $ lemma-⋖+-trim'-equal r⋖+s x'<m x'<n ⟩
                    NFRestrToℕ (trim' r x'<m)
                ≡⟨ sym $ resurface-correctness r x'<m x'<m ⟩
                    (just $ NFSToℕ $ resurface r x'<m) 
                ∎

    -- The ReplaceRespLocal filter requires that the normal form
    -- of y equals `replace y x x'` in case there exists some x ⊂ y
    -- that is related to some x' < x.
    -- But multiple such replacement pairs (x , x') may exist,
    -- and the filter only explicitly states the constraint for the
    -- lexicographically least (x , x').
    -- However, it indirectly inductively follows that the filter requires
    -- y to be related to `replace y w w'` for ANY replacement pair (w , w'),
    -- (provided that the NFRestr so far satisfies the filter at every point).
    ReplaceRespLocal-anyreplacement
        : {y : ℕ}
        → (h : (n : ℕ) → NFRestr n)
        → (H : (n : ℕ) → h n ⋖ h (ℕ.suc n))
        → Exence-sats ReplaceRespLocal (h , H)
        → {x x' : ℕ}
        → x ⊂ y
        → x' < x
        → AreRelated (h y) x x'
        → choiceToℕ (getChoiceFromExence (h , H) y)
          ≡ 
          choiceToℕ (getChoiceFromExence (h , H) (replace T y x x'))

    ReplaceRespLocal-anyreplacement {y*} h H LocSat {x*} {x*'} =
        <<<-rec P recursion (y* , x* , x*')
        where
            f : ℕ → ℕ
            -- Same as: f  ≔ proj₁ (combine (h , H))
            f n = choiceToℕ (getChoiceFromExence (h , H) n) 

            Goal : ℕ → ℕ → ℕ → Set
            Goal y x x' = choiceToℕ (getChoiceFromExence (h , H) y) 
                   ≡ 
                   choiceToℕ (getChoiceFromExence (h , H) (replace T y x x'))

            P : (ℕ × ℕ × ℕ) → Set
            P (y , z , z') = 
                  z ⊂ y
                → z' < z
                → AreRelated (h y) z z'
                → Goal y z z'

            cases 
                : (y x x' : ℕ)
                → ({ s : (ℕ × ℕ × ℕ) } → s <<< (y , x , x') → P s)
                → (p : AllArgsNormal (h y) ⊎ MinNonNormalArg (h y)) 
                → (p ≡ allArgsNormal? (h y)) 
                → P (y , x  , x')

            cases y x x' IH (inj₁ allNormal) p-eq x⊂y x'<x xRx' = 
                ⊥-elim $ allNormal x x⊂y (x' , x'<x , xRx')
            cases y x x' IH 
                  (inj₂ (w , w⊂y , w' , w'<w , wRw' , isMin)) p-eq 
                  x⊂y x'<x xRx' 
                  = subcases (isMin x x' x⊂y x'<x xRx')
                  where

                    yx  : ℕ
                    yx  = replace T y x x'
                    yxw : ℕ
                    yxw = replace T yx w w'
                    yw  : ℕ
                    yw  = replace T y w w'
                    ywx : ℕ
                    ywx = replace T yw x x'
                    ywxw : ℕ
                    ywxw = replace T ywx w w'

                    yx<y : yx < y
                    yx<y = replace-< T y x x' x⊂y x'<x
                    yw<y : yw < y
                    yw<y = replace-< T y w w' w⊂y w'<w

                    yx,w,w'<<<y,x,x' : (yx , w , w') <<< (y , x , x')
                    yx,w,w'<<<y,x,x' = first-<-to-<<< yx w w' y x x' yx<y
                    
                    yw,x,x'<<<y,x,x' : (yw , x , x') <<< (y , x , x')
                    yw,x,x'<<<y,x,x' = first-<-to-<<< yw x x' y x x' yw<y


                    xR[yw]x' : AreRelated (h yw) x x'
                    xR[yw]x' = areRelated-in-restriction (h yw) (h y) 
                        (lemma-⋖+-exence h H yw<y) x'<x xRx'

                    wR[yx]w' : AreRelated (h yx) w w'
                    wR[yx]w' = areRelated-in-restriction (h yx) (h y) 
                        (lemma-⋖+-exence h H yx<y) w'<w wRw'

                    subcases 
                        : (w < x) ⊎ (w ≡ x × w' < x') ⊎ (w ≡ x × w' ≡ x') 
                        → Goal y x x'
                    subcases (inj₁ w<x) = ans 
                        where
                            y,w,w'<<<y,x,x' : (y , w , w') <<< (y , x , x')
                            y,w,w'<<<y,x,x' = second-<-to-<<< y w w' x x' w<x
                            
                            x≢w : x ≢ w
                            x≢w refl = n≮n x w<x

                            x⊂yw : x ⊂ yw
                            x⊂yw = keep T y w w' x w⊂y x⊂y (≢-sym x≢w)

                            ywx<y : ywx < y
                            ywx<y = <-trans (replace-< T yw x x' x⊂yw x'<x) yw<y
                    
                            ywx,w,w'<<<y,x,x' : (ywx , w , w') <<< (y , x , x')
                            ywx,w,w'<<<y,x,x' = first-<-to-<<< ywx w w' y x x' ywx<y

                            wR[ywx]w' : AreRelated (h ywx) w w'
                            wR[ywx]w' = areRelated-in-restriction (h ywx) (h y) 
                                (lemma-⋖+-exence h H ywx<y) w'<w wRw'

                            x≢w' : x ≢ w'
                            x≢w' = λ eq → (n≮n x 
                                (<-trans (subst (_< w) (sym eq) w'<w) w<x)) 

                            fyxw≡fywx : f yxw ≡ f ywx
                            fyxw≡fywx = subsubcases (w ≟ x')
                                where
                                    subsubcases : Dec (w ≡ x') → f yxw ≡ f ywx
                                    subsubcases (no w≢x') = cong f $ sym $ 
                                        comm T y x x' w w' x⊂y w⊂y 
                                            x≢w'
                                            w≢x'
                                    subsubcases (yes refl) = 
                                        sym $ 
                                        begin 
                                            f ywx
                                        ≡⟨ sub-eq ⟩
                                            f ywxw
                                        ≡⟨ cong f $ lemma-replace-wxw y w w'
                                           x x' (≢-sym x≢w') 
                                         ⟩
                                            f yxw
                                        ∎
                                        where
                                            sub-eq : f ywx ≡ f ywxw
                                            sub-eq with w ⊂? ywx
                                            ... | yes w⊂ywx = 
                                                IH ywx,w,w'<<<y,x,x' w⊂ywx w'<w 
                                                   wR[ywx]w'
                                            ... | no w⊄ywx = 
                                                cong f 
                                                    $ noeff T ywx w w' 
                                                    $ not-true-to-is-false w⊄ywx
                            w⊂yx : w ⊂ yx
                            w⊂yx = keep T y x x' w x⊂y w⊂y x≢w

                            ans : Goal y x x'
                            ans = sym $
                                begin 
                                    f yx 
                                ≡⟨ IH yx,w,w'<<<y,x,x' w⊂yx w'<w wR[yx]w' ⟩
                                    f yxw
                                ≡⟨ fyxw≡fywx ⟩
                                    f ywx
                                ≡⟨ sym $ IH yw,x,x'<<<y,x,x' x⊂yw x'<x xR[yw]x' ⟩
                                    f yw
                                ≡⟨ sym $ IH y,w,w'<<<y,x,x' w⊂y w'<w wRw' ⟩
                                    f y
                                ∎
                    subcases(inj₂ (inj₁ (x≡w@refl , w'<x'))) = 
                        begin 
                            f y
                        ≡⟨ IH y,w,w'<<<y,x,x' w⊂y w'<w wRw' ⟩
                            f yw
                        ≡⟨ cong f $ noeff T yw x x' x⊄yw ⟩
                            f ywx
                        ≡⟨ cong f $ comm T y x x' w w' x⊂y w⊂y x≢w' w≢x' ⟩
                            f yxw
                        ≡⟨ cong f $ sym $ noeff T yx w w' w⊄yx ⟩
                            f yx
                        ∎
                        where
                            -- Note that x ≡ w in this case!
                            x≢w' : x ≢ w'
                            x≢w' refl = n≮n x w'<w

                            w≢x' : w ≢ x'
                            w≢x' refl = n≮n w x'<x

                            x⊄yw : x ⊄ yw
                            x⊄yw = complete T y x w' x≢w' x⊂y

                            w⊄yx : w ⊄ yx
                            w⊄yx = complete T y x x' w≢x' w⊂y
                        
                            y,w,w'<<<y,x,x'
                                : (y , w , w') <<< (y , x , x')
                            y,w,w'<<<y,x,x' = third-<-to-<<< y x w' x' w'<x'

                    subcases(inj₂ (inj₂ (refl , refl))) = fy≡fyw
                        where
                            nf-yx : Choices (h y)
                            nf-yx = earlier-new $ resurface (h y) yx<y

                            -- This is the choice that the ReplaceRespLocal
                            -- filter enforces equality to. 
                            nf-yw : Choices (h y)
                            nf-yw = earlier-new $ resurface (h y) yw<y

                            eq : yx ≡ yw
                            eq = refl

                            ⊂-<-irrel : (y z z' : ℕ) 
                                → Relation.Nullary.Irrelevant ((z ⊂ y) × (z' < z))
                            ⊂-<-irrel y z z' = irrel-×-closure 
                                (⊂-irrelevant {z} {y}) 
                                (<-irrelevant {z'} {z})


                            A : Set
                            A = Σ[ t ∈ ℕ × ℕ ] 
                                (proj₁ t ⊂ y) × (proj₂ t < proj₁ t)

                            tuplesEq : _≡_ {A = A} ((w , w') , w⊂y , w'<w)
                                                   ((x , x') , x⊂y , x'<x)
                            tuplesEq = restIsProofIrrel {A = ℕ × ℕ} 
                                {B = λ (z , z') → (z ⊂ y) × (z' < z)}
                                (λ (z , z') → ⊂-<-irrel y z z')
                                (w⊂y , w'<w)
                                (x⊂y , x'<x)
                                refl

                            nf-yw≡nf-yx : nf-yw ≡ nf-yx
                            nf-yw≡nf-yx = 
                                begin 
                                nf-yw
                                ≡⟨⟩
                                    (earlier-new $ resurface (h y)
                                        $ replace-< T y w w' w⊂y w'<w )
                                ≡⟨⟩
                                    auxfun ((w , w') , w⊂y , w'<w)
                                ≡⟨ cong auxfun tuplesEq ⟩
                                    auxfun ((x , x') , x⊂y , x'<x)
                                ≡⟨⟩
                                    (earlier-new $ resurface (h y)
                                        $ replace-< T y x x' x⊂y x'<x )
                                ≡⟨⟩
                                    nf-yx
                                ∎
                                where
                                    auxfun : A → Choices (h y)
                                    auxfun ((z , z') , z⊂y , z'<z)
                                        = earlier-new 
                                            $ resurface (h y)
                                            $ replace-< T y z z' z⊂y z'<z
                                        
                                
                                                   


                            g : (n : ℕ) → Choices (h n)
                            g = getChoiceFromExence (h , H)

                            gy≡nf-yx : g y ≡ nf-yx
                            gy≡nf-yx = decEqReflection _≡?_ (g y) nf-yx $
                                sym $
                                begin 
                                    true
                                ≡⟨ sym $ LocSat y ⟩
                                    ReplaceRespLocal (h y) (g y)
                                ≡⟨⟩
                                    ReplaceRespLocal-cases (h y) (g y) 
                                        (forgetMinimality 
                                        $ allArgsNormal? (h y))
                                ≡⟨ cong (λ t → ReplaceRespLocal-cases (h y) (g y) 
                                        (forgetMinimality t )) (sym p-eq) ⟩
                                    ReplaceRespLocal-cases (h y) (g y) 
                                        (forgetMinimality 
                                        $ (inj₂ (w , w⊂y , w' , w'<w , wRw' , isMin)))
                                ≡⟨⟩
                                    ReplaceRespLocal-cases (h y) (g y) 
                                        (inj₂ (w , w' , w⊂y , w'<w , wRw'))
                                ≡⟨⟩
                                    does (g y ≡? nf-yw)
                                ≡⟨ cong (λ v → does (g y ≡? v)) nf-yw≡nf-yx ⟩
                                    does (g y ≡? nf-yx)
                                ∎

                            fy≡fyw : f y ≡ f yw
                            fy≡fyw =
                                begin 
                                    f y
                                ≡⟨⟩
                                    choiceToℕ (getChoiceFromExence (h , H) y)
                                ≡⟨ cong choiceToℕ gy≡nf-yx ⟩
                                    choiceToℕ (earlier-new $ resurface (h y) yx<y)
                                ≡⟨⟩
                                    NFSToℕ (resurface (h y) yx<y)
                                ≡⟨ lemma-resurface-getChoice h H yx<y ⟩
                                    choiceToℕ (getChoiceFromExence (h , H) yx)
                                ≡⟨⟩
                                    f yx
                                ∎
                                

            recursion 
                : (t : ℕ × ℕ × ℕ) 
                → ({ s : (ℕ × ℕ × ℕ) } → s <<< t → P s)
                → P t
            recursion (y , x , x') IH
                = cases y x x' IH (allArgsNormal? (h y)) refl


    -- Variant of above lemma where an NFFun instead of an Exence is given.
    ReplaceRespLocal-anyreplacement-NFFun
        : {y : ℕ}
        → (f' : NFFun)
        → NFFun-sats ReplaceRespLocal f'
        → {x x' : ℕ}
        → x ⊂ y
        → x' < x
        → (proj₁ $ FunToRel f') x x' ≡ true
        → proj₁ f' y
          ≡ 
          proj₁ f' (replace T y x x')
    ReplaceRespLocal-anyreplacement-NFFun {y} f' LocSat {x} {x'} x⊂y x'<x xRx'  
        = ans
        where
            areRelated : AreRelated (restrict f' y) x x'
            areRelated = lemma-FunToRel-AreRelated f' x x' xRx' y
            f = proj₁ f'
            h = proj₁ (restrict+ f')
            H = proj₂ (restrict+ f')
            almost : choiceToℕ (getChoiceFromExence (h , H) y)
                     ≡ 
                     choiceToℕ (getChoiceFromExence (h , H) (replace T y x x'))
            almost = ReplaceRespLocal-anyreplacement h H LocSat {x} {x'} x⊂y 
                                                     x'<x areRelated
            ans =
                begin 
                    f y
                ≡⟨ sym $ theo-combine∘restrict+ f' y ⟩
                    choiceToℕ (getChoiceFromExence (h , H) y)
                ≡⟨ almost ⟩
                    choiceToℕ (getChoiceFromExence (h , H) (replace T y x x'))
                ≡⟨ theo-combine∘restrict+ f' (replace T y x x') ⟩
                    f (replace T y x x')
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
        → (p : AllArgsNormal (restrict f' y) ⊎ MinNonNormalArg (restrict f' y))
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
            ReplaceRespLocal-cases r c (forgetMinimality $ allArgsNormal? r)
        ≡⟨ cong (ReplaceRespLocal-cases r c) 
            (cong forgetMinimality $ sym p≡allArgsNormal?) ⟩
            ReplaceRespLocal-cases r c (inj₁ normal)
        ≡⟨⟩
            true
        ∎
        
    theo-ReplaceResp-left-cases f'@(f , f-leq , f-fix) y 
                                (inj₂ p@(x , x⊂y , x' , x'<x , xRx' , isMin)) 
                                p≡allArgsNormal? G =
        begin 
            ReplaceRespLocal r c
        ≡⟨⟩
            ReplaceRespLocal-cases r c (forgetMinimality $ allArgsNormal? r)
        ≡⟨ cong (ReplaceRespLocal-cases r c) 
            (cong forgetMinimality $ sym p≡allArgsNormal?) ⟩
            ReplaceRespLocal-cases r c ((forgetMinimality $ inj₂ p))
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
            fy≡fy' = ReplaceRespLocal-anyreplacement-NFFun f'
                                                     LocSat
                                                     x⊂y
                                                     x'<x
                                                     xRx'

            -- By definition of ReplaceRespLocal-cases,
            -- the following is only possible if fy-as-choice
            -- equals `earlier-new $ resurface r y'<y`.
            -- We know this is not the case since `p` proves that f y ≢ f y'
            -- (where y'  ≔ replace y x x').
            satAty : ReplaceRespLocal {y} (restrict f' y) fy-as-choice ≡ true
            satAty = LocSat y

            contra : ⊥
            contra = fy≢fy' fy≡fy'

    ----------------------------------------------------------------------------
    -- The congruence filter is 'DeadEndFree'; following
    -- allowed choices will not get stuck.
    ----------------------------------------------------------------------------
    -- Strategy: introduce a new normal form when the filters allows it;
    -- otherwise it only allows one choice, and then we pick that one.
    --
    -- Note: when following this strategy from the start,
    -- then the congruence-constraint will never apply because every argument
    -- is its own normal form, and the filter will continue to allow introducing
    -- new normal forms.
    -- In other words, this strategy encodes the identity relation.
    -- (The other extreme, relating everything to 0, should also be possible).
    ----------------------------------------------------------------------------
    ReplaceRespLocal-DeadEndFree : DeadEndFree ReplaceRespLocal
    ReplaceRespLocal-DeadEndFree {y} r LocSat = cases (allArgsNormal? r) refl
        where
            F = ReplaceRespLocal
            cases
                : (p : AllArgsNormal r ⊎ MinNonNormalArg r)
                → (allArgsNormal? r ≡ p)
                → Σ[ c ∈ Choices r ] F Allows c In r
            cases (inj₁ allNormal) p-eq = (here , allowed)
                where
                    allowed : F Allows here In r
                    allowed = 
                        begin 
                            F r here
                        ≡⟨⟩
                            ReplaceRespLocal-cases r here 
                                (forgetMinimality $ allArgsNormal? r)
                        ≡⟨ cong  (λ x → ReplaceRespLocal-cases r here 
                                (forgetMinimality x)) p-eq ⟩
                            ReplaceRespLocal-cases r here (inj₁ allNormal)
                        ≡⟨⟩
                            true
                        ∎
            cases (inj₂ (x , x⊂y , x' , x'<x , xRx' , isMin)) p-eq 
                = (c , allowed)
                where
                    yx : ℕ
                    yx = replace T y x x'

                    yx<y : yx < y
                    yx<y = replace-< T y x x' x⊂y x'<x

                    c : Choices r
                    c = earlier-new $ resurface r yx<y

                    allowed : F Allows c In r
                    allowed = 
                        begin 
                            F r c
                        ≡⟨⟩
                            ReplaceRespLocal-cases r c 
                                (forgetMinimality $ allArgsNormal? r)
                        ≡⟨ cong  (λ x → ReplaceRespLocal-cases r c 
                                (forgetMinimality x)) p-eq ⟩
                            ReplaceRespLocal-cases r c 
                                (forgetMinimality 
                                $ inj₂ (x , x⊂y , x' , x'<x , xRx' , isMin))
                        ≡⟨⟩
                            ReplaceRespLocal-cases r c 
                                (inj₂ (x , x' , x⊂y , x'<x , xRx' ))
                        ≡⟨⟩
                            does (c ≡? c) 
                        ≡⟨ decEqCoReflection _≡?_ c c refl ⟩
                            true
                        ∎
                        
        
