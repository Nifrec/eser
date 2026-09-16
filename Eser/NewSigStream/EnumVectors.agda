-- Module      : Eser.NewSigStream.EnumVectors
-- Description : Enumerate ℕ-vectors of same length and same sum.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
{-# OPTIONS --termination-depth=2 #-}

open import Level hiding (suc)
open import Data.Nat
open import Data.Nat.Properties
open import Data.Sum hiding (map)
open import Data.Product hiding (map)
open import Data.Empty
open import Data.Fin using (Fin ; _↑ˡ_ ; _↑ʳ_ )
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning renaming (begin_ to ≡begin_ ; _∎ to _≡∎)
open import Data.Vec as Vec
open import Data.Vec.Properties
open import Data.List.Membership.Propositional
open import Data.List renaming (_∷_ to _∷L_) hiding (sum)
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

mapp
    : {A B : Set} 
    → (A → B)
    → Σ[ n ∈ ℕ ] Vec A (suc n)
    → Σ[ n ∈ ℕ ] Vec B (suc n)
mapp {A} {B} f (n , v) = (n , Vec.map f v)

--_w∷_ : {m w n : ℕ} → {v : Vec ℕ m} → (weight v ≡ w) → (X : WVec m w n) → WVec m w (suc n)
--_w∷_ {v = v} eq X = (v , eq) Vec.∷ X

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
        fun : WVec m 0
            → WVec (suc m) 0
        fun (v , eq) = (0 ∷ v , eq)
        output = mapp fun rec
getWVec (suc m) (suc w) = 
    -- Add one more weight point to the current position.
    mapp incrFirst (getWVec (suc m) w)
    +++
    -- Don't drop any more weight here, and move to the next position.
    mapp (0 w∷_) (getWVec m (suc w))
    module PosWeightCase where
        incrFirst : {m w : ℕ} → WVec m w → WVec m (suc w)
        incrFirst (x ∷ xs , eq) = ((suc x) ∷ xs , cong suc eq)
has-weight-irrel 
    : {m : ℕ}
    → (w : ℕ)
    → (v : Vec ℕ m)
    → Relation.Nullary.Irrelevant (weight v ≡ w)
has-weight-irrel w v p q = uip p q

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
        outp : Vec.lookup (Vec.map fun vecs) j ≡ (0 ∷ xs , eq)
        outp =
            ≡begin 
                Vec.lookup (Vec.map fun vecs) j
            ≡⟨ lookup-map j fun vecs  ⟩
                fun (Vec.lookup vecs j)
            ≡⟨ cong fun $ proj₂ IH ⟩
                fun (xs , eq)
            ≡⟨⟩
                (0 ∷ xs , eq)
            ≡∎
-- If the first element of v is 0, then v is constructed in the RHS
-- of the +++ in the (suc m) (suc w) case of getWVec.
getWVec-complete {suc m} {suc w} (ℕ.zero ∷ xs , eq) = (j , outp)
    where
        open PosWeightCase m w
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
        open PosWeightCase m w
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


-- Simple implementation that does not come with internal correctness proofs.
enumVecs : (m w : ℕ) → List (Vec ℕ (suc m))
    -- Drop all remaining weights in only remaining cell.
enumVecs 0 w = Data.List.[ w ∷ [] ]
    -- We are out of budget, fill the rest of the vector with 0s.
enumVecs (suc m) 0 = Data.List.map (0 ∷_) (enumVecs m 0)
enumVecs (suc m) (suc w) = 
    -- Drop one more weight at the current position.
    Data.List.map incrFirst (enumVecs (suc m) w)
    Data.List.++
    -- Don't drop any more weight here, and move to the next position.
    Data.List.map (0 ∷_) (enumVecs m (suc w))
    where
        incrFirst : {m : ℕ} → Vec ℕ (suc m) → Vec ℕ (suc m)
        incrFirst (x ∷ xs) = (suc x) ∷ xs

test = enumVecs 3 3

forgetWeight : {m w : ℕ} → WVec m w → Vec ℕ (suc m)
forgetWeight (v , eq) = v

vecPart : (m : ℕ) → Partition (Vec ℕ (suc m))
vecPart m = record { chunks = chunks ; complete = {! !} ; unique = {! !} }
    where
        chunks : Chunking (Vec ℕ (suc m))
        chunks w = (proj₁ wvecs , Vec.map forgetWeight (proj₂ wvecs))
            where
                wvecs : Σ[ n ∈ ℕ ] Vec (WVec m w) (suc n)
                wvecs = getWVec m w
