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
        -- Arguments are always smaller than the while construction.
        ⊂-resp-< : (y x : ℕ) → x is-arg-of y ≡ true → x < y
        replace : ℕ → ℕ → ℕ → ℕ
        -- Replacing an argument by a smaller alternative reduces
        -- the size of the whole construction.
        replace-< 
            : (y x x' : ℕ) 
            → (x is-arg-of y ≡ true) 
            → (x' < x) 
            → (replace y x x' < y)
        -- Replacing one argument keeps the other arguments in place.
        keep 
            : (y x x' z : ℕ) 
            → (x is-arg-of y ≡ true) 
            → (z is-arg-of y ≡ true) 
            → (x ≢ z)
            → (z is-arg-of (replace y x x') ≡ true)
        
        -- Negative analog of keep : when replacing x, and x'≢z,
        -- then z does not become an argument.
        nospawn 
            : (y x x' z : ℕ) 
            → (z is-arg-of y ≡ false) 
            → (x' ≢ z)
            → (z is-arg-of (replace y x x') ≡ false)
        -- When performing two non-overlapping replacements
        -- (the replacement of one is not the replacecant of the other),
        -- their order does not matter.
        comm
            : (y x x' z z' : ℕ) 
            → (x is-arg-of y ≡ true) 
            → (z is-arg-of y ≡ true) 
            → (x ≢ z')
            → (z ≢ x')
            → (replace (replace y z z') x x') ≡ (replace (replace y x x') z z')

        noeff
            : (y x x' : ℕ) 
            → (x is-arg-of y ≡ false) 
            → y ≡ replace y x x'

        -- The 'real' cut rule follows from this and the other rules, 
        -- see below as a lemma.
        halfcut
            : (y x z a : ℕ)
            → replace (replace y x a) a z ≡ replace (replace y x z) a z

        id-rep
            : (y x : ℕ)
            → replace y x x ≡ y

        -- The replacement completely replaces ALL instances of an argument.
        complete
            : (y x x' : ℕ)
            → x ≢ x'
            → (x is-arg-of y ≡ true) 
            → (x is-arg-of (replace y x x')) ≡ false
open ReplaceStruct

module ReplaceStructLemmas (T : ReplaceStruct) where
    rep : ℕ → ℕ → ℕ → ℕ
    rep = replace T

    _⊂_ : ℕ → ℕ → Set
    _⊂_ n m = (_is-arg-of_ T) n m ≡ true

    _⊄_ : ℕ → ℕ → Set
    n ⊄ m = (_is-arg-of_ T) n m ≡ false

    _⊂?_ : (n m : ℕ) → Dec (n ⊂ m)
    n ⊂? m = ⊂?-cases (_is-arg-of_ T n m) refl
        where
            ⊂?-cases : (b : Bool) → (_is-arg-of_ T n m ≡ b) → Dec (n ⊂ m)
            ⊂?-cases true p = true because ofʸ p
            ⊂?-cases false p = false because ofⁿ 
                (is-false-to-not-true p)

    cut
        : (y x z a : ℕ)
        → a ⊄ y
        → replace T (replace T y x a) a z ≡ replace T y x z
    cut y x z a a⊄y = 
        begin 
            rep (rep y x a) a z
        ≡⟨ halfcut T y x z a ⟩
            rep (rep y x z) a z
        ≡⟨ eq (z ≟ a ) ⟩
            rep y x z
        ∎
        where
            eq : Dec (z ≡ a) → rep (rep y x z) a z ≡ rep y x z
            eq (yes refl) = id-rep T (rep y x z) a
            eq (no  z≢a) = sym $ noeff T (rep y x z) a z a⊄y'
                where
                    a⊄y' : a  ⊄ (rep y x z)
                    a⊄y' = nospawn T y x z a a⊄y z≢a

    idempotent
        : (y x x' x'' : ℕ)
        → x ≢ x'
        → rep (rep y x x') x x'' ≡ rep y x x'
    idempotent y x x' x'' x≢x' = sym $ noeff T (rep y x x') x x'' x⊄yx
        where
            x⊄yx : x ⊄ (rep y x x')
            x⊄yx with x ⊂? y
            ... | yes x⊂y = complete T y x x' x≢x' x⊂y
            ... | no ¬x⊂y = ans
                where
                    x⊄y = not-true-to-is-false ¬x⊂y
                    y≡yx : y ≡ rep y x x'
                    y≡yx = noeff T y x x' x⊄y

                    ans : x ⊄ (rep y x x')
                    ans = subst (x ⊄_) y≡yx x⊄y

        
        
            
    -- Performing one replacement, then another, and then the first one again,
    -- has the same effect as only doing the last two replacements,
    -- provided that the middle replacement does not target the output of the first.
    lemma-replace-wxw
        : (y w w' x x' : ℕ)
        → w' ≢ x
        → replace T (replace T (replace T y w w') x x') w w' 
          ≡ 
          replace T (replace T y x x') w w'
    lemma-replace-wxw y w w' x x' w'≢x = 
        cases (w ≟ w') (w ⊂? y) (x ⊂? y) (w ≟ x')
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

            cases 
                : Dec (w ≡ w')
                → Dec (w ⊂ y)
                → Dec (x ⊂ y)
                → Dec (w ≡ x')
                → ywxw ≡ yxw
            cases (yes refl) _ _ _ = 
                cong (λ y → rep (rep y x x') w w') (id-rep T y w)
            cases (no w≢w') (no w⊄y) _ _ = 
                cong (λ y → rep (rep y x x') w w') (sym $ noeff T y w w' 
                $ not-true-to-is-false w⊄y)
            cases (no w≢w') (yes w⊂y) (no x⊄y) _ = 
                begin 
                    rep (rep (rep y w w') x x') w w'
                ≡⟨ cong (λ y → rep y w w') $ sym $ noeff T (rep y w w') x x' 
                   $ nospawn T y w w' x (not-true-to-is-false x⊄y) w'≢x
                 ⟩
                    rep (rep y w w') w w'
                ≡⟨ idempotent y w w' w' w≢w' ⟩
                    rep y w w'
                ≡⟨ cong (λ y → rep y w w') 
                   $ noeff T y x x' 
                   $ not-true-to-is-false x⊄y
                 ⟩
                    rep (rep y x x') w w'
                ∎
                
            cases (no w≢w') (yes w⊂y) (yes x⊂y) (no w≢x') =
                begin 
                    rep (rep (rep y w w') x x') w w'
                ≡⟨ cong (λ y → rep y w w') 
                   $ comm T y x x' w w' x⊂y w⊂y (≢-sym w'≢x) w≢x'
                 ⟩
                    rep (rep (rep y x x') w w') w w'
                ≡⟨ idempotent (rep y x x') w w' w' w≢w' ⟩
                    rep (rep y x x') w w'
                ∎
            cases (no w≢w') (yes w⊂y) (yes x⊂y) (yes refl) = 
                begin 
                    rep (rep (rep y w w') x x') w w'
                ≡⟨⟩
                    
                    rep (rep (rep y w w') x w) w w'
                ≡⟨ cut (rep y w w') x w' w w⊄yw ⟩
                    rep (rep y w w') x w'
                ≡⟨ comm T y x w' w w' x⊂y w⊂y (≢-sym w'≢x) w≢w' ⟩
                    rep (rep y x w') w w'
                ≡⟨ (sym $ halfcut T y x w' w) ⟩
                    rep (rep y x w) w w'
                ≡⟨⟩
                    rep (rep y x x') w w'
                ∎
                where
                    w⊄yw : w ⊄ (rep y w w')
                    w⊄yw = complete T y w w' w≢w' w⊂y

    ⊂-irrelevant : Relation.Binary.Irrelevant _⊂_
    ⊂-irrelevant p q = uip p q

-- Unused laws that would also make sense to more strictly describe term
-- algebras:
record ReplaceStructUnneededLawsCollection : Set where
    field
        -- These are copied from ReplaceStruct; 
        -- if ReplaceStructUnneededLawsCollection is ever to be used, 
        -- one had better merge the two records
        -- or give this one a parameter/field of value ReplaceStruct.
        _is-arg-of_ : ℕ → ℕ → Bool
        replace : ℕ → ℕ → ℕ → ℕ

        monotone
            : (y x x' x'' : ℕ)
            → (x is-arg-of y ≡ true) 
            → x' < x''
            → replace y x x' < replace y x x''
    

--------------------------------------------------------------------------------
-- 𝟐. Predicate 'ReplaceResp'
--------------------------------------------------------------------------------
module ReplaceResp (T : ReplaceStruct) where
    open ReplaceStructLemmas T

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

    IsNormalisable
        : {x y : ℕ}
        → (r : NFRestr y)
        → x < y
        → Set
    IsNormalisable {x} {y} r x<y = Σ[ x' ∈ ℕ ] (x' < x) × (AreRelated r x x')

    -- Proof-relevant predicate that there exists an
    -- x' smaller than x itself, such that x'<x and r relates x' and x.
    -- If at least one such an x' exists, return the minimal one.
    IsMinNormalisable
        : {y : ℕ}
        → (r : NFRestr y)
        → ℕ
        → Set
    IsMinNormalisable {y} r x =
        Σ[ x' ∈ ℕ ] 
            (x' < x) 
            × (AreRelated r x x')
            -- All other alternatives are bigger or equal.
            × (
                (x'' : ℕ) 
                → (x'' < x) 
                → AreRelated r x x''
                → (x' < x'') ⊎ (x'' ≡ x')
            )
    IsMinNormalisableArg
        : {y : ℕ}
        → (r : NFRestr y)
        → ℕ
        → Set
    IsMinNormalisableArg {y} r x =
        x ⊂ y
        × Σ[ x' ∈ ℕ ] 
            (x' < x) 
            × (AreRelated r x x')
            -- All other normalisable pairs are bigger or equal.
            × ((w w' : ℕ) → (w ⊂ y) → (w' < w) → AreRelated r w w'
                →
                (x < w)
                ⊎
                (x ≡ w × x' < w')
                ⊎
                (x ≡ w × x' ≡ w')
                )


    -- Check if the normal form of a number is equal to itself.
    IsNormal
        : {x y : ℕ}
        → (r : NFRestr y)
        → x < y
        → Set
    IsNormal {x} {y} r x<y = ¬ IsNormalisable r x<y

    isNormal?
        : {x y : ℕ}
        → (r : NFRestr y)
        → (x<y : x < y)
        → IsNormal r x<y ⊎ IsMinNormalisable r x
    isNormal? {x} {y} r x<y = isNormal?-rec x ≤-refl
        where
            OutType : ℕ → Set
            OutType w = 
                  ¬ (Σ[ x' ∈ ℕ ] (x' < w) × AreRelated r x x') 
                  ⊎ 
                  IsMinNormalisable r x
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
                    cases (inj₁ p) (yes w'Rx) = inj₂ minNonNormal
                        where
                            isMin 
                                : (v : ℕ) 
                                → v < x 
                                → AreRelated r x v 
                                → w' < v ⊎ v ≡ w'
                            isMin v v<x xRv with <-cmp v w' 
                            ... | tri< v<w _ _ = ⊥-elim $ p (v , v<w , xRv)
                            ... | tri≈ _ v≡w _ = inj₂ v≡w
                            ... | tri> _ _ w<v = inj₁ w<v
                            minNonNormal : IsMinNormalisable r x
                            minNonNormal = (w' , w'<x , w'Rx , isMin)

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

    -- Proof-relevant predicate that y had a SMALLEST argument
    -- x for which there exists an x'<x s.t. x' is related to x.
    MinNonNormalArg
        : {y : ℕ}
        → (r : NFRestr y)
        → Set
    MinNonNormalArg {y} r = Σ[ x ∈ ℕ ] IsMinNormalisableArg r x

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
        → AllSmallerNormal r x ⊎ MinNonNormalArg r
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
                : (p : AllSmallerNormal r x' ⊎ MinNonNormalArg r)
                → (p ≡ allArgsNormal?Rec x' y r x'<y)
                → (Dec (x ⊂ y))
                → AllSmallerNormal r x ⊎ MinNonNormalArg r
            allArgsNormal?Rec-cases-x⊂y 
                : (p : AllSmallerNormal r x')
                → x ⊂ y
                → AllSmallerNormal r x ⊎ MinNonNormalArg r

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
            ... | inj₂ (x'' , x''<x , xRx'' , isMin')  
                = inj₂ minNonNormalArg
                    where
                        isMin 
                            : (w w' : ℕ) 
                            → (w ⊂ y) 
                            → (w' < w) 
                            → AreRelated r w w'
                            → (x < w) ⊎ (x ≡ w × x'' < w') ⊎ (x ≡ w × x'' ≡ w')
                        isMin w w' w⊂y w'<w wRw' with <-cmp x w
                        ... | tri< x<w _ _ = inj₁ x<w
                        ... | tri> _ _ w<x = 
                                ⊥-elim $ allSmallerNorm w (s≤s⁻¹ w<x) w⊂y 
                                                        (w' , w'<w , wRw')
                        ... | tri≈ _ refl _ with <-cmp x'' w'
                        ... |   tri< x''<w' _ _ = inj₂ (inj₁ (refl , x''<w'))
                        ... |   tri≈ _ refl _ = inj₂ (inj₂ (refl , refl))
                        ... |   tri> _ _ w'<x'' with (isMin' w' w'<w wRw')
                        ... |     inj₁ x''<w' = 
                                        ⊥-elim $ n≮n x'' (<-trans x''<w' w'<x'')
                        ... |     inj₂ refl = 
                                        ⊥-elim $ n≮n x'' w'<x''

                        minNonNormalArg : MinNonNormalArg r
                        minNonNormalArg = (x , x⊂y , x'' , x''<x , xRx'' , 
                                           isMin)


    -- Test if some argument of y has a normal form (accoding to r)
    -- not equal to itself.
    -- Implementation: just brute force check all x < y by induction.
    allArgsNormal?
        : {y : ℕ}
        → (r : NFRestr y)
        → AllArgsNormal r ⊎ MinNonNormalArg r
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

    forgetMinimality 
        : {y : ℕ}
        → {r : NFRestr y}
        → AllArgsNormal r ⊎ MinNonNormalArg r 
        → AllArgsNormal r ⊎ NonNormalArg r 
    forgetMinimality {y} {r} (inj₁ p) = inj₁ p
    forgetMinimality {y} {r} (inj₂ (x , x⊂y , x' , x'<x , xRx' , minimality)) 
        = inj₂ (x , x' , x⊂y , x'<x , xRx' )


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
