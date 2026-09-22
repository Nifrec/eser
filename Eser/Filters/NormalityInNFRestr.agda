-- Module      : Eser.Filters.NormalityInNFRestr
-- Description : Normality and relatedness of elements of NFRestr.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- Definition of 'AreRelated' in an NFRestr: an `r : NFRestr n` encodes
-- a partial equivalence relation, two elements are related according to r 
-- if they have the same normal form. 
-- Elements greater or equal to n, which are not assigned a normal form in r,
-- are always considered related (for convenience).
--
-- An element in r is 'normal' if its normal form is itself
-- (predicate IsNormal).
--
-- Given a replacement structure, define the notion of `AllArgsNormal`;
-- predicate on an element y that holds if all all arguments of y (all x s.t.
-- x ⊂ y) are normal in r.
--
-- IsNormal and AllArgsNormal are decidable (functions `isNormal?` and
-- `allArgsNormal?`).
--
-- Also versions with 'Min': these come with the minimum witness of being
-- non-normal (being 'normalisible') or the minimum normalisible argument.

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

module Eser.Filters.NormalityInNFRestr where
    
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

module NormalityForReplStruct (T : ReplaceStruct) where
    open ReplaceStructLemmas T
    open ReplaceStruct

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

    forgetMinimality 
        : {y : ℕ}
        → {r : NFRestr y}
        → AllArgsNormal r ⊎ MinNonNormalArg r 
        → AllArgsNormal r ⊎ NonNormalArg r 
    forgetMinimality {y} {r} (inj₁ p) = inj₁ p
    forgetMinimality {y} {r} (inj₂ (x , x⊂y , x' , x'<x , xRx' , minimality)) 
        = inj₂ (x , x' , x⊂y , x'<x , xRx' )


