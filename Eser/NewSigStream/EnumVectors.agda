-- Module      : Eser.NewSigStream.EnumVectors
-- Description : Enumerate ℕ-vectors of same length and same sum.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------

-- #EXT: This option is needed for getWVec-complete.
-- I do not understand why, this function takes two ℕ
-- arguments, matches them up to a depth of 1,
-- and makes only recursive calls with exactly one of the two decreased by 1 and
-- the other unchanged. Refactoring this function can probably alliviate the
-- need for the termination depth increase.
{-# OPTIONS --termination-depth=2 #-}

open import Level hiding (suc)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Data.Empty
open import Data.Fin using (Fin ; _↑ˡ_ ; _↑ʳ_ ; splitAt ; join)
open import Data.Fin.Properties using (join-splitAt)
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)
open import Data.Vec as Vec hiding (splitAt)
open import Data.Vec.Properties
open import Data.List.Membership.Propositional
open import Data.List renaming (_∷_ to _∷L_) hiding (sum ; splitAt)
open import Function hiding (_↔_)

open import Eser.Logic
open import Eser.Aux using (restIsProofIrrel ; uip)
open import Eser.Equivalences.Notation

module Eser.NewSigStream.EnumVectors where

Chunking : (A : Set) → Set
Chunking A = ℕ → Σ[ m ∈ ℕ ] Vec A (suc m)

SubIdx : {A : Set} → Chunking A → ℕ → Set
SubIdx f i = Fin (suc $ proj₁ $ f i)

Idx : {A : Set} → Chunking A → Set
Idx f = Σ[ i ∈ ℕ ] (SubIdx f i)

_!!!_ : {A : Set} → (f : Chunking A) → Idx f → A
f !!! (i , j) = Vec.lookup (proj₂ $ f i) j

record Partition (A : Set) : Set where
    field
        chunks : Chunking A
        -- Each element occurs in some chunk.
        complete : (a : A) → Σ[ ij ∈ (Idx chunks) ] a ≡ chunks !!! ij
        -- Chunks are disjoint and have no duplicates,
        -- i.e., elements occur in at most one chunk and therein at most once.
        unique 
            : (ij hk : Idx chunks) 
            → (chunks !!! ij) ≡ (chunks !!! hk) 
            → ij ≡ hk

partitionToEnum : {A : Set} → Partition A → A ≃ ℕ
partitionToEnum {A} p = ?

-- The weight of a Vec ℕ is the sum of its elements.
weight : {m : ℕ} → Vec ℕ m → ℕ
weight = Vec.sum

-- Vector of length 1+m that has weight w.
WVec : ℕ → ℕ → Set
WVec m w =  Σ[ v ∈ Vec ℕ (suc m) ] weight v ≡ w

_w∷_ : {m w : ℕ} → (n : ℕ) → (v : WVec m w) → WVec (suc m) (n + w)
n w∷ (v , eq) = (n Vec.∷ v , cong (n +_) eq)

_+++_ 
    : {A : Set} 
    → Σ[ n ∈ ℕ ] Vec A (suc n) 
    → Σ[ n ∈ ℕ ] Vec A (suc n)
    → Σ[ n ∈ ℕ ] Vec A (suc n)
(n , v) +++ (m , u) = (n + suc m , v Vec.++ u)

has-weight-irrel 
    : {m : ℕ}
    → (w : ℕ)
    → (v : Vec ℕ m)
    → Relation.Nullary.Irrelevant (weight v ≡ w)
has-weight-irrel w v p q = uip p q

mapp
    : {A B : Set} 
    → (A → B)
    → Σ[ n ∈ ℕ ] Vec A (suc n)
    → Σ[ n ∈ ℕ ] Vec B (suc n)
mapp {A} {B} f (n , v) = (n , Vec.map f v)

zero-cons : {m w : ℕ} → (WVec m w) → (WVec (suc m) w)
zero-cons (v , eq) = (0 ∷ v , eq)

incrFirst : {m w : ℕ} → WVec m w → WVec m (suc w)
incrFirst (x ∷ xs , eq) = ((suc x) ∷ xs , cong suc eq)

incrFirst-injective
    : {m w : ℕ}
    → {v u : WVec m w}
    → (incrFirst v ≡ incrFirst u)
    → v ≡ u
incrFirst-injective {m} {w} {x ∷ xs , eq-v} {y ∷ ys , eq-u} eq = ans
    where
        x≡y : x ≡ y
        x≡y = suc-injective $ cong (λ (v , _) → Vec.head v) eq
        xs≡ys : xs ≡ ys
        xs≡ys = cong (λ (v , _) → Vec.tail v) eq
        xxs≡yys : x ∷ xs ≡ y ∷ ys
        xxs≡yys = cong₂ _∷_ x≡y xs≡ys
        ans : (x ∷ xs , eq-v) ≡ (y ∷ ys , eq-u)
        ans = restIsProofIrrel (has-weight-irrel w) eq-v eq-u xxs≡yys

zero-w-cons-injective
    : {m w : ℕ}
    → {v u : WVec m w}
    → 0 w∷ v ≡ 0 w∷ u
    → v ≡ u
zero-w-cons-injective {m} {w} {x ∷ xs , eq-v} {y ∷ ys , eq-u} eq = ans
    where
        x≡y : x ≡ y
        x≡y = cong (λ (v , _) → Vec.head $ Vec.tail v) eq
        xs≡ys : xs ≡ ys
        xs≡ys = cong (λ (v , _) → Vec.tail $ Vec.tail v) eq
        xxs≡yys : x ∷ xs ≡ y ∷ ys
        xxs≡yys = cong₂ _∷_ x≡y xs≡ys
        ans : (x ∷ xs , eq-v) ≡ (y ∷ ys , eq-u)
        ans = restIsProofIrrel (has-weight-irrel w) eq-v eq-u xxs≡yys


-- More notation heavy implementation that comes with proofs that:
-- * The output is a non-empty list (of length suc n),
-- * of non-empty vectors (of length suc m),
-- * all of weight w.
-- Note: these always exist, in the extreme case where m ≗ 0
-- we may still output a vector of length 1, and indeed [ w ] works.
getWVec : (m w : ℕ) → Σ[ n ∈ ℕ ] Vec (WVec m w) (suc n)
-- Drop all remaining weights in only remaining cell.
getWVec 0 w = (0 , (w Vec.∷ Vec.[] , +-identityʳ w) ∷ Vec.[])
-- We are out of budget, fill the rest of the vector with 0s.
getWVec (suc m) 0 = output
    module ZeroWeightCase where
        rec : Σ[ n ∈ ℕ ] Vec (WVec m 0) (suc n)
        rec = getWVec m 0
        output = mapp zero-cons rec
getWVec (suc m) (suc w) = 
    -- Add one more weight point to the current position.
    mapp incrFirst (getWVec (suc m) w)
    +++
    -- Don't drop any more weight here, and move to the next position.
    mapp (0 w∷_) (getWVec m (suc w))

getWVec-complete 
    : {m w : ℕ}
    → (v : WVec m w)
    → Σ[ j ∈ (Fin $ suc $ proj₁ $ getWVec m w) ] 
        Vec.lookup (proj₂ $ getWVec m w) j ≡ v
getWVec-complete {ℕ.zero} {w} v@(x ∷ [] , refl) = (Fin.zero , eq)
    where
        lemma : (v v' : Vec ℕ 1) → (weight v ≡ weight v') → v ≡ v'
        lemma (y ∷ []) (z ∷ []) eq = cong (_∷ []) y≡z
            where
                y≡z : y ≡ z
                y≡z = 
                    ≡begin 
                        y
                    ≡⟨ sym $ +-identityʳ y ⟩
                        y + 0
                    ≡⟨ eq ⟩
                        z + 0
                    ≡⟨ +-identityʳ z ⟩
                        z
                    ≡∎
        irrel 
            : (v : Vec ℕ 1)
            → Relation.Nullary.Irrelevant (weight v ≡ w)
        irrel = has-weight-irrel {1} w
        eq' : (w ∷ []) ≡ (x Vec.∷ [])
        eq' = lemma (w ∷ []) (x Vec.∷ []) (+-identityʳ w)
        eq : (w ∷ [] , +-identityʳ w) ≡ v
        eq = restIsProofIrrel irrel (+-identityʳ w) (refl) eq'
getWVec-complete {suc m} {ℕ.zero} (0 ∷ xs , eq) = (j , outp)
    where
        open ZeroWeightCase m
        n : ℕ
        n = suc $ proj₁ $ rec
        vecs : Vec (WVec m 0) n
        vecs = proj₂ rec
        IH : Σ[ j ∈ Fin n ] Vec.lookup vecs j ≡ (xs , eq)
        IH = getWVec-complete {m} {0} (xs , eq)
        j : Fin n
        j = proj₁ IH
        outp : Vec.lookup (Vec.map zero-cons vecs) j ≡ (0 ∷ xs , eq)
        outp =
            ≡begin 
                Vec.lookup (Vec.map zero-cons vecs) j
            ≡⟨ lookup-map j zero-cons vecs  ⟩
                zero-cons (Vec.lookup vecs j)
            ≡⟨ cong zero-cons $ proj₂ IH ⟩
                zero-cons (xs , eq)
            ≡⟨⟩
                (0 ∷ xs , eq)
            ≡∎
-- If the first element of v is 0, then v is constructed in the RHS
-- of the +++ in the (suc m) (suc w) case of getWVec.
getWVec-complete {suc m} {suc w} (ℕ.zero ∷ xs , eq) = (j , outp)
    where
        rec-l : Σ[ n ∈ ℕ ] Vec (WVec (suc m) w) (suc n)
        rec-l = getWVec (suc m) w
        n-l : ℕ
        n-l = suc $ proj₁ rec-l
        vecs-l : Vec (WVec (suc m) w) n-l
        vecs-l = proj₂ rec-l

        rec-r : Σ[ n ∈ ℕ ] Vec (WVec m  (suc w)) (suc n)
        rec-r = getWVec m (suc w)
        n-r : ℕ
        n-r = suc $ proj₁ rec-r
        vecs-r : Vec (WVec m (suc w)) n-r
        vecs-r = proj₂ rec-r

        IH : Σ[ j' ∈ Fin n-r ] Vec.lookup vecs-r j' ≡ (xs , eq)
        IH = getWVec-complete {m} {suc w} (xs , eq)
        j' : Fin n-r
        j' = proj₁ IH
        j : Fin (n-l + n-r)
        j = n-l ↑ʳ j'

        vecs = Vec.map incrFirst vecs-l Vec.++ Vec.map (0 w∷_) vecs-r

        outp : Vec.lookup vecs j ≡ (0 ∷ xs , eq)
        outp =
            ≡begin 
                Vec.lookup vecs j
            ≡⟨ lookup-++ʳ 
                (Vec.map incrFirst vecs-l)
                (Vec.map (0 w∷_) vecs-r)
                j'
            ⟩
                Vec.lookup (Vec.map (0 w∷_) vecs-r) j'
            ≡⟨ lookup-map j' (0 w∷_) vecs-r  ⟩
                0 w∷ (Vec.lookup vecs-r j')
            ≡⟨ cong (0 w∷_) $ proj₂ IH ⟩
                0 w∷ (xs , eq)
            ≡⟨⟩
                (0 ∷ xs , cong (0 +_) eq)
            ≡⟨ restIsProofIrrel (has-weight-irrel (suc w)) 
                                (cong (0 +_) eq) eq refl ⟩
                (0 ∷ xs , eq)
            ≡∎
-- If the first element of v is suc x, then v is constructed in the LHS
-- of the +++ in the (suc m) (suc w) case of getWVec.
-- #EXT: there is quite some redundancy between this case and the previous case.
getWVec-complete {suc m} {suc w} (suc x ∷ xs , eq) = (j , outp)
    where
        rec-l : Σ[ n ∈ ℕ ] Vec (WVec (suc m) w) (suc n)
        rec-l = getWVec (suc m) w
        n-l : ℕ
        n-l = suc $ proj₁ rec-l
        vecs-l : Vec (WVec (suc m) w) n-l
        vecs-l = proj₂ rec-l

        rec-r : Σ[ n ∈ ℕ ] Vec (WVec m  (suc w)) (suc n)
        rec-r = getWVec m (suc w)
        n-r : ℕ
        n-r = suc $ proj₁ rec-r
        vecs-r : Vec (WVec m (suc w)) n-r
        vecs-r = proj₂ rec-r

        eq' : weight (x ∷ xs) ≡ w
        eq' = suc-injective eq
        IH : Σ[ j' ∈ Fin n-l ] Vec.lookup vecs-l j' ≡ (x ∷ xs , eq')
        IH = getWVec-complete {suc m} {w} (x ∷ xs , eq')
        j' : Fin n-l
        j' = proj₁ IH
        j : Fin (n-l + n-r)
        j = j' ↑ˡ n-r

        vecs = Vec.map incrFirst vecs-l Vec.++ Vec.map (0 w∷_) vecs-r

        outp : Vec.lookup vecs j ≡ (suc x ∷ xs , eq)
        outp =
            ≡begin 
                Vec.lookup vecs j
            ≡⟨ lookup-++ˡ
                (Vec.map incrFirst vecs-l)
                (Vec.map (0 w∷_) vecs-r)
                j'
            ⟩
                Vec.lookup (Vec.map incrFirst vecs-l) j'
            ≡⟨ lookup-map j' incrFirst vecs-l  ⟩
                incrFirst (Vec.lookup vecs-l j')
            ≡⟨ cong incrFirst $ proj₂ IH ⟩
                incrFirst (x ∷ xs , eq')
            ≡⟨⟩
                (suc x ∷ xs , cong suc eq')
            ≡⟨ restIsProofIrrel (has-weight-irrel (suc w)) 
                                (cong suc eq') eq refl ⟩
                (suc x ∷ xs , eq)
            ≡∎

zero-cons-injective 
    : {m w : ℕ}
    → {v v' : WVec m w}
    → zero-cons v ≡ zero-cons v'
    → v ≡ v'
zero-cons-injective {m} {w} {v , eq-v} {v' , eq-v'} eq = 
    restIsProofIrrel (has-weight-irrel w) eq-v eq-v' v≡v'
    where
        v≡v' : v ≡ v'
        v≡v' = ∷-injectiveʳ (cong proj₁ eq)

getWVec-unique
    : {m w : ℕ}
    → (i j : (Fin $ suc $ proj₁ $ getWVec m w))
    → Vec.lookup (proj₂ $ getWVec m w) i ≡ Vec.lookup (proj₂ $ getWVec m w) j
    → i ≡ j
getWVec-unique {ℕ.zero} {w} Fin.zero Fin.zero refl = refl
getWVec-unique {suc m} {ℕ.zero} i j eq = getWVec-unique {m} {ℕ.zero} i j eq'
    where
        n : ℕ
        n = suc $ proj₁ $ getWVec m 0
        vecs : Vec (WVec m 0) n
        vecs = proj₂ $ getWVec m 0
        eq' : Vec.lookup vecs i 
              ≡ 
              Vec.lookup vecs j
        eq' = zero-cons-injective $
            ≡begin 
               zero-cons (Vec.lookup vecs i)
            ≡⟨ sym $ lookup-map i zero-cons vecs  ⟩
                Vec.lookup (Vec.map zero-cons vecs) i
            ≡⟨ eq ⟩
                Vec.lookup (Vec.map zero-cons vecs) j
            ≡⟨ lookup-map j zero-cons vecs  ⟩
              zero-cons (Vec.lookup vecs j)
            ≡∎
getWVec-unique {suc m} {suc w} i j eq = 
    cases (splitAt n-l i) (splitAt n-l j) refl refl
    where
        n : ℕ
        n = suc $ proj₁ $ getWVec (suc m) (suc w)
        vecs : Vec (WVec (suc m) (suc w)) n
        vecs = proj₂ $ getWVec (suc m) (suc w)

        n-l : ℕ
        n-l = suc $ proj₁ $ getWVec (suc m) w
        LHS' : Vec (WVec (suc m) w) n-l
        LHS' = proj₂ $ getWVec (suc m) w
        LHS : Vec (WVec (suc m) (suc w)) n-l
        LHS = Vec.map incrFirst $ LHS'

        n-r : ℕ
        n-r = suc $ proj₁ $ getWVec m (suc w)
        RHS' : Vec (WVec m (suc w)) n-r
        RHS' = proj₂ $ getWVec m (suc w)
        RHS : Vec (WVec (suc m) (suc w)) n-r
        RHS = Vec.map (0 w∷_) RHS'

        check : n ≡ n-l + n-r × vecs ≡ LHS Vec.++ RHS
        check = (refl , refl)

        Hi : Vec.lookup (LHS Vec.++ RHS) i 
             ≡ 
             [ Vec.lookup LHS , Vec.lookup RHS ]′ (splitAt n-l i)
        Hi = lookup-splitAt n-l LHS RHS i

        Hj : Vec.lookup (LHS Vec.++ RHS) j
             ≡ 
             [ Vec.lookup LHS , Vec.lookup RHS ]′ (splitAt n-l j)
        Hj = lookup-splitAt n-l LHS RHS j

        incrFirst-firstelem-nonzero
            : {m w : ℕ}
            → (v : WVec m w)
            → Vec.head (proj₁ (incrFirst v)) ≢ 0
        incrFirst-firstelem-nonzero {m} {w} (x ∷ xs , _) = 1+n≢0 {x}

        incrFirst-firstelem-nonzero'
            : {m w n : ℕ}
            → (v : WVec m (suc w))
            → (vecs : Vec (WVec m w) n)
            → (i : Fin n)
            → (v ≡ Vec.lookup (Vec.map incrFirst vecs) i)
            → Vec.head (proj₁ v) ≢ 0
        incrFirst-firstelem-nonzero' v vecs i eq = ans
            where
                H : v ≡ incrFirst (Vec.lookup vecs i)
                H = trans eq $ lookup-map i incrFirst vecs
                ans = subst 
                    (λ v → Vec.head (proj₁ v) ≢ 0) 
                    (sym H)
                    $ incrFirst-firstelem-nonzero (Vec.lookup vecs i)

        zero-w-cons-firstelem-nonsuc
            : {m w : ℕ}
            → (v : WVec m w)
            → (y : ℕ)
            → Vec.head (proj₁ (0 w∷ v)) ≢ suc y
        zero-w-cons-firstelem-nonsuc {m} {w} (x ∷ xs , _) y = ≢-sym $ 1+n≢0 {y}

        zero-w-cons-firstelem-nonsuc'
            : {m w n y : ℕ}
            → (v : WVec (suc m) w)
            → (vecs : Vec (WVec m w) n)
            → (i : Fin n)
            → (v ≡ Vec.lookup (Vec.map (0 w∷_) vecs) i)
            → Vec.head (proj₁ v) ≢ suc y
        zero-w-cons-firstelem-nonsuc' {y = y} v vecs i eq = ans
            where
                H : v ≡ 0 w∷ (Vec.lookup vecs i)
                H = trans eq $ lookup-map i (0 w∷_) vecs
                ans = subst 
                    (λ v → Vec.head (proj₁ v) ≢ suc y) 
                    (sym H)
                    $ zero-w-cons-firstelem-nonsuc (Vec.lookup vecs i) y

        -- The LHS has only elements whose first element is incremented,
        -- and the RHS has only elements whose first element is 0.
        -- Clearly no vector can be in both!
        LHS-RHS-disjointness 
            : (i : Fin n-l)
            → (j : Fin n-r)
            → (v : WVec (suc m) (suc w))
            → v ≡ Vec.lookup LHS i
            → v ≡ Vec.lookup RHS j
            → ⊥
        LHS-RHS-disjointness i j v@(ℕ.zero ∷ xs , eq) p q = 
            incrFirst-firstelem-nonzero' v LHS' i p refl 
        LHS-RHS-disjointness i j v@(suc x ∷ xs , eq) p q =
            zero-w-cons-firstelem-nonsuc' v RHS' j q refl 

        i'≡j'→i≡j 
            : ( i' j' : Fin n-l ⊎ Fin n-r )
            → (i' ≡ splitAt n-l i)
            → (j' ≡ splitAt n-l j)
            → i' ≡ j'
            → i ≡ j
        i'≡j'→i≡j i' j' eq-i eq-j i'≡j' = 
            ≡begin 
                i
            ≡⟨ sym $ join-splitAt n-l n-r i ⟩
                join n-l n-r (splitAt n-l i)
            ≡⟨ cong (join n-l n-r) $ sym eq-i ⟩
                join n-l n-r i'
            ≡⟨ cong (join n-l n-r) i'≡j' ⟩
                join n-l n-r j'
            ≡⟨ sym $ cong (join n-l n-r) $ sym eq-j ⟩
                join n-l n-r (splitAt n-l j)
            ≡⟨ join-splitAt n-l n-r j ⟩
               j 
            ≡∎
            

        cases
            : ( i' j' : Fin n-l ⊎ Fin n-r )
            → (i' ≡ splitAt n-l i)
            → (j' ≡ splitAt n-l j)
            → i ≡ j
        -- First case: follows from IH and injectivity of incrFirst.
        cases (inj₁ i') (inj₁ j') eq-i eq-j = 
            i'≡j'→i≡j (inj₁ i') (inj₁ j') eq-i eq-j (cong inj₁ $ IH lookup-eq)
            where
                IH : Vec.lookup LHS' i' 
                     ≡ 
                     Vec.lookup LHS' j'
                    → i' ≡ j'
                IH = getWVec-unique {suc m} {w} i' j'
                lookup-eq  
                    : Vec.lookup LHS' i' 
                     ≡ 
                     Vec.lookup LHS' j'
                lookup-eq = incrFirst-injective $ 
                    ≡begin 
                      incrFirst (Vec.lookup LHS' i')
                    ≡⟨ sym $ lookup-map i' incrFirst LHS' ⟩
                        Vec.lookup (Vec.map incrFirst LHS') i'
                    ≡⟨⟩
                        Vec.lookup LHS i'
                    ≡⟨⟩
                        [ Vec.lookup LHS , Vec.lookup RHS ]′ (inj₁ i')
                    ≡⟨ cong ([ Vec.lookup LHS , Vec.lookup RHS ]′) eq-i ⟩
                        [ Vec.lookup LHS , Vec.lookup RHS ]′ (splitAt n-l i)
                    ≡⟨ sym $ Hi ⟩
                        Vec.lookup (LHS Vec.++ RHS) i
                    ≡⟨ eq ⟩
                        Vec.lookup (LHS Vec.++ RHS) j
                    ≡⟨ Hj ⟩
                        [ Vec.lookup LHS , Vec.lookup RHS ]′ (splitAt n-l j)
                    ≡⟨ cong ([ Vec.lookup LHS , Vec.lookup RHS ]′) (sym eq-j) ⟩
                        [ Vec.lookup LHS , Vec.lookup RHS ]′ (inj₁ j')
                    ≡⟨⟩
                        Vec.lookup LHS j'
                    ≡⟨⟩
                        Vec.lookup (Vec.map incrFirst LHS') j'
                    ≡⟨ lookup-map j' incrFirst LHS' ⟩
                        incrFirst (Vec.lookup LHS' j')
                    ≡∎

        cases (inj₁ i') (inj₂ j') eq-i eq-j = 
            ⊥-elim $ LHS-RHS-disjointness i' j' v eq-v-i eq-v-j
            where
                v : WVec (suc m) (suc w)
                v = Vec.lookup LHS i'
                eq-v-i = refl
                eq-v-j : v ≡ Vec.lookup RHS j'
                eq-v-j = 
                    ≡begin 
                        v 
                    ≡⟨⟩
                        Vec.lookup LHS i'
                    ≡⟨⟩
                        [ Vec.lookup LHS , Vec.lookup RHS ]′ (inj₁ i')
                    ≡⟨ cong ([ Vec.lookup LHS , Vec.lookup RHS ]′) eq-i ⟩
                        [ Vec.lookup LHS , Vec.lookup RHS ]′ (splitAt n-l i)
                    ≡⟨ sym $ Hi ⟩
                        Vec.lookup (LHS Vec.++ RHS) i
                    ≡⟨ eq ⟩
                        Vec.lookup (LHS Vec.++ RHS) j
                    ≡⟨ Hj ⟩
                        [ Vec.lookup LHS , Vec.lookup RHS ]′ (splitAt n-l j)
                    ≡⟨ cong ([ Vec.lookup LHS , Vec.lookup RHS ]′) (sym eq-j) ⟩
                        [ Vec.lookup LHS , Vec.lookup RHS ]′ (inj₂ j')
                    ≡⟨⟩
                        Vec.lookup RHS j'
                    ≡∎
        -- Same as prev case, but with i' and j', and i and j swapped, and `sym
        -- eq` instead of `eq`.
        cases (inj₂ i') (inj₁ j') eq-i eq-j = 
            ⊥-elim $ LHS-RHS-disjointness j' i' v eq-v-j eq-v-i
            where
                v : WVec (suc m) (suc w)
                v = Vec.lookup LHS j'
                eq-v-j = refl
                eq-v-i : v ≡ Vec.lookup RHS i'
                eq-v-i = 
                    ≡begin 
                        v 
                    ≡⟨⟩
                        Vec.lookup LHS j'
                    ≡⟨⟩
                        [ Vec.lookup LHS , Vec.lookup RHS ]′ (inj₁ j')
                    ≡⟨ cong ([ Vec.lookup LHS , Vec.lookup RHS ]′) eq-j ⟩
                        [ Vec.lookup LHS , Vec.lookup RHS ]′ 
                            (splitAt n-l j)
                    ≡⟨ sym $ Hj ⟩
                        Vec.lookup (LHS Vec.++ RHS) j
                    ≡⟨ sym $ eq ⟩
                        Vec.lookup (LHS Vec.++ RHS) i
                    ≡⟨ Hi ⟩
                        [ Vec.lookup LHS , Vec.lookup RHS ]′ 
                            (splitAt n-l i)
                    ≡⟨ cong ([ Vec.lookup LHS , Vec.lookup RHS ]′) (sym eq-i) ⟩
                        [ Vec.lookup LHS , Vec.lookup RHS ]′ (inj₂ i')
                    ≡⟨⟩
                        Vec.lookup RHS i'
                    ≡∎
        -- Last case: similar to first case; use IH and injectivity of (0 w∷_).
        -- Now we need to use the RHS instead of the LHS.
        cases (inj₂ i') (inj₂ j') eq-i eq-j =
            i'≡j'→i≡j (inj₂ i') (inj₂ j') eq-i eq-j (cong inj₂ $ IH lookup-eq)
            where
                IH : Vec.lookup RHS' i' 
                     ≡ 
                     Vec.lookup RHS' j'
                    → i' ≡ j'
                IH = getWVec-unique {m} {suc w} i' j'
                lookup-eq  
                    : Vec.lookup RHS' i' 
                     ≡ 
                     Vec.lookup RHS' j'
                lookup-eq = zero-w-cons-injective $ 
                    ≡begin 
                      (0 w∷_) (Vec.lookup RHS' i')
                    ≡⟨ sym $ lookup-map i' (0 w∷_) RHS' ⟩
                        Vec.lookup (Vec.map (0 w∷_) RHS') i'
                    ≡⟨⟩
                        Vec.lookup RHS i'
                    ≡⟨⟩
                        [ Vec.lookup LHS , Vec.lookup RHS ]′ (inj₂ i')
                    ≡⟨ cong ([ Vec.lookup LHS , Vec.lookup RHS ]′) eq-i ⟩
                        [ Vec.lookup LHS , Vec.lookup RHS ]′ (splitAt n-l i)
                    ≡⟨ sym $ Hi ⟩
                        Vec.lookup (LHS Vec.++ RHS) i
                    ≡⟨ eq ⟩
                        Vec.lookup (LHS Vec.++ RHS) j
                    ≡⟨ Hj ⟩
                        [ Vec.lookup LHS , Vec.lookup RHS ]′ (splitAt n-l j)
                    ≡⟨ cong ([ Vec.lookup LHS , Vec.lookup RHS ]′) (sym eq-j) ⟩
                        [ Vec.lookup LHS , Vec.lookup RHS ]′ (inj₂ j')
                    ≡⟨⟩
                        Vec.lookup RHS j'
                    ≡⟨⟩
                        Vec.lookup (Vec.map (0 w∷_) RHS') j'
                    ≡⟨ lookup-map j' (0 w∷_) RHS' ⟩
                        (0 w∷_) (Vec.lookup RHS' j')
                    ≡∎
        
        


-- Simple implementation that does not come with internal correctness proofs.
enumVecs : (m w : ℕ) → List (Vec ℕ (suc m))
    -- Drop all remaining weights in only remaining cell.
enumVecs 0 w = Data.List.[ w ∷ [] ]
    -- We are out of budget, fill the rest of the vector with 0s.
enumVecs (suc m) 0 = Data.List.map (0 ∷_) (enumVecs m 0)
enumVecs (suc m) (suc w) = 
    -- Drop one more weight at the current position.
    Data.List.map incrFirst' (enumVecs (suc m) w)
    Data.List.++
    -- Don't drop any more weight here, and move to the next position.
    Data.List.map (0 ∷_) (enumVecs m (suc w))
    where
        incrFirst' : {m : ℕ} → Vec ℕ (suc m) → Vec ℕ (suc m)
        incrFirst' (x ∷ xs) = (suc x) ∷ xs

test = enumVecs 3 3

forgetWeight : {m w : ℕ} → WVec m w → Vec ℕ (suc m)
forgetWeight (v , eq) = v

forgetWeight-injective
    : {m w : ℕ}
    → (v u : WVec m w)
    → forgetWeight v ≡ forgetWeight u
    → v ≡ u
forgetWeight-injective {m} {w} (v , pv) (v , pu) refl = 
    restIsProofIrrel (has-weight-irrel w) pv pu refl


vecPart : (m : ℕ) → Partition (Vec ℕ (suc m))
vecPart m = record { chunks = chunks ; complete = complete ; unique = unique }
    where
        chunks : Chunking (Vec ℕ (suc m))
        chunks w = (proj₁ wvecs , Vec.map forgetWeight (proj₂ wvecs))
            where
                wvecs : Σ[ n ∈ ℕ ] Vec (WVec m w) (suc n)
                wvecs = getWVec m w
        complete 
            : (v : Vec ℕ (suc m))
            → Σ[ ij ∈ Idx chunks ] (v ≡ chunks !!! ij)
        complete v = ((w , j) , sym eq)
            where
                w : ℕ
                w = weight v
                u : WVec m w
                u = (v , refl)
                
                -- Size minus 1 of the chunk containing the vectors of weight w.
                n : ℕ
                n = proj₁ $ getWVec m w

                vecs : Vec (WVec m w) (suc n)
                vecs = proj₂ $ getWVec m w

                j : Fin (suc n)
                j = proj₁ $ getWVec-complete u

                eq-u : Vec.lookup vecs j ≡ u
                eq-u = proj₂ $ getWVec-complete u

                eq : chunks !!! (w , j) ≡ v
                eq =
                    ≡begin 
                        chunks !!! (w , j)
                    ≡⟨⟩
                        Vec.lookup (Vec.map forgetWeight vecs) j
                    ≡⟨ lookup-map j forgetWeight vecs ⟩
                        forgetWeight (Vec.lookup vecs j)
                    ≡⟨ cong forgetWeight $ eq-u ⟩
                        forgetWeight u
                    ≡⟨⟩
                        v 
                    ≡∎
        unique
            : (wi w'j : Idx chunks)
            → (chunks !!! wi) ≡ (chunks !!! w'j) 
            → wi ≡ w'j
        unique wi@(w , i) w'j@(w' , j) eq = lemma w≡w' i j eq
            where
                v' : WVec m w
                v' = Vec.lookup (proj₂ $ getWVec m w) i
                v : Vec ℕ (suc m)
                v = (chunks !!! wi)
                Hv : proj₁ v' ≡ v
                Hv = 
                    ≡begin 
                        proj₁ v'
                    ≡⟨⟩
                        forgetWeight (Vec.lookup (proj₂ $ getWVec m w) i)
                    ≡⟨ sym $ lookup-map i forgetWeight (proj₂ $ getWVec m w) ⟩
                        Vec.lookup (Vec.map forgetWeight 
                                    (proj₂ $ getWVec m w)) i
                    ≡⟨⟩
                        chunks !!! wi
                    ≡∎

                u' : WVec m w'
                u' = Vec.lookup (proj₂ $ getWVec m w') j
                u : Vec ℕ (suc m)
                u = (chunks !!! w'j)
                Hu : proj₁ u' ≡ u
                Hu = 
                    ≡begin 
                        proj₁ u'
                    ≡⟨⟩
                        forgetWeight (Vec.lookup (proj₂ $ getWVec m w') j)
                    ≡⟨ sym $ lookup-map j forgetWeight (proj₂ $ getWVec m w') ⟩
                        Vec.lookup (Vec.map forgetWeight 
                                    (proj₂ $ getWVec m w')) j
                    ≡⟨⟩
                        chunks !!! w'j
                    ≡∎

                w≡w' : w ≡ w'
                w≡w' = 
                    ≡begin 
                        w
                    ≡⟨ (sym $ proj₂ $ Vec.lookup (proj₂ $ getWVec m w) i) ⟩
                        weight (proj₁ v')
                    ≡⟨ cong weight Hv ⟩
                        weight v
                    ≡⟨ cong weight eq ⟩
                        weight u
                    ≡⟨ cong weight $ sym Hu ⟩
                        weight (proj₁ u')
                    ≡⟨ (proj₂ $ Vec.lookup (proj₂ $ getWVec m w') j) ⟩
                        w'
                    ≡∎
                lemma
                    : {w w' : ℕ}
                    → w ≡ w'
                    → (i : SubIdx chunks w)
                    → (j : SubIdx chunks w')
                    → chunks !!! (w , i) ≡ chunks !!! (w' , j)
                    → (w , i) ≡ (w' , j)
                lemma {w} {w} refl i j eq = cong (w ,_) i≡j
                    where
                        x : Vec ℕ (suc m)
                        x = forgetWeight $ Vec.lookup (proj₂ $ getWVec m w) i
                        y : Vec ℕ (suc m)
                        y = forgetWeight $ Vec.lookup (proj₂ $ getWVec m w) j
                        eq'' : x ≡ y
                        eq'' =
                            ≡begin 
                                forgetWeight 
                                    (Vec.lookup (proj₂ $ getWVec m w) i)
                            ≡⟨ sym $ lookup-map i forgetWeight 
                                                (proj₂ $ getWVec m w) ⟩
                                Vec.lookup 
                                (Vec.map forgetWeight $ proj₂ $ getWVec m w) i
                            ≡⟨ eq ⟩
                                Vec.lookup 
                                (Vec.map forgetWeight $ proj₂ $ getWVec m w) j
                            ≡⟨ lookup-map j forgetWeight 
                                                (proj₂ $ getWVec m w) ⟩
                                forgetWeight 
                                    (Vec.lookup (proj₂ $ getWVec m w) j)
                            ≡∎
                            
                        eq' : Vec.lookup (proj₂ $ getWVec m w) i 
                              ≡ 
                              Vec.lookup (proj₂ $ getWVec m w) j
                        eq' = forgetWeight-injective 
                                (Vec.lookup (proj₂ $ getWVec m w) i) 
                                (Vec.lookup (proj₂ $ getWVec m w) j) 
                                eq''
                        i≡j : i ≡ j
                        i≡j = getWVec-unique {m} {w} i j eq'
