-- Module      : StreamGrids.Test.List
-- Description : Testcases for StreamGrids.List
-- Copyright   : (c) Lulof Pirée, 2025
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------


module StreamGrids.Test.List where

-- TODO: probably not all of these are needed.
open import Data.Bool hiding (_≤_; _≤?_)
open import Data.Empty
open import Data.Fin hiding (_<_)
open import Function using (Inverseᵇ)
open import Data.List
open import Data.Nat hiding (_<_)
open import Data.Nat.Properties
open import Data.Product
open import Data.Sum
open import Data.Unit
open import Level using (0ℓ)
open import Relation.Binary.Core using (Rel)
open import Relation.Binary.Definitions
open import Relation.Binary.PropositionalEquality hiding ([_])
open import Relation.Nullary


open import StreamGrids.List


DL : List (List ℕ)
DL = ( 1 ∷ 2 ∷ 3 ∷ [] ) ∷ ( 4 ∷ 5 ∷ 6 ∷ [] ) ∷ []
-- Indices live in Fin n, not in ℕ, so we cannot use arabics as notation...
testGetEL : DL ,, (suc zero) ,, (suc (suc zero)) ≡ 6
testGetEL = refl

SL : List ℕ
SL = 2 ∷ 0 ∷ 2 ∷ 5 ∷ []
SLAtOneIsZero : 0 ∈ SL
SLAtOneIsZero = (suc zero) , refl

testGetListIdx : getListIdx SLAtOneIsZero ≡ suc zero
testGetListIdx = refl

test∈∈ : 6 ∈∈ DL
test∈∈ = (suc zero , suc (suc zero) , refl) -- 6 occurs at index pair (1, 2).

testFlatLength : flatLength DL ≡ 6
testFlatLength = refl

testGetSuperIndex : (getSuperListIdx test∈∈) ≡ (fromℕ 1)
testGetSuperIndex = refl

--------------------------------------------------------------------------------
-- Test listRelat
--------------------------------------------------------------------------------

L : List (List ℕ)
L = (( 2 ∷ 4 ∷ 0 ∷ 8 ∷ []) ∷ (1 ∷ 9  ∷ 6 ∷ 7 ∷ []) ∷ [])

8∈∈L : 8 ∈∈ L
8∈∈L = (zero , fromℕ 3 , refl)

0∈∈L : 0 ∈∈ L
0∈∈L = (zero , suc (suc zero) , refl)

4∈∈L : 4 ∈∈ L
4∈∈L = (zero , suc zero , refl)

1∈∈L : 1 ∈∈ L
1∈∈L = (fromℕ 1 , zero , refl)

7∈∈L : 7 ∈∈ L
7∈∈L = (fromℕ 1 , fromℕ 3 , refl)

testListRelat1 : (L ⊢ 8 ≈ 0)
testListRelat1 = (8∈∈L , 0∈∈L , refl)

-- Same as first test, but with LHS and RHS interchanged: ≈ ought to be
-- symmetric.
testListRelat2 : L ⊢ 0 ≈ 8
testListRelat2 = (0∈∈L , 8∈∈L , refl)

-- Also check second sublist.
testListRelat3 : L ⊢ 1 ≈ 7
testListRelat3 = (1∈∈L , 7∈∈L , refl)


-- Elements not in the list should never be related to anything.
testListRelat4 : ¬ (L ⊢ 3 ≈ 8)
testListRelat4 (3∈∈L , _) = lemma 3∈∈L
    where
        -- This lemma basically needs to brute-force check ALL incides of the
        -- list, and see none holds element 3.
        lemma : ¬ (3 ∈∈ L)
        lemma (zero , suc (suc (suc zero)) , ())
        lemma (zero , suc (suc (suc (suc ()))) , Lij=3)
        lemma (suc zero , suc (suc (suc zero)) , ())
        lemma (suc zero , suc (suc (suc (suc ()))) , Lij=3)

lemmap4 : (p : 4 ∈∈ L) → (proj₁ p ≡ zero)
lemmap4 (zero , _) = refl
lemmap4 (suc zero , suc (suc (suc zero)) , ())
lemmap4 (suc zero , suc (suc (suc (suc ()))) , _)

lemmap7 : (p : 7 ∈∈ L) → (proj₁ p ≡ suc zero)
lemmap7 (zero , suc (suc (suc zero)) , ())
lemmap7 (zero , suc (suc (suc (suc ()))) , _)
lemmap7 (suc zero , j , k) = refl

-- This is just to help Agda with figuring out the types in `lemmaZeroIsNotOne`.
-- The expression `¬ (zero ≡ suc zero)` is ambigous; are we in ℕ, or in Fin n?
-- And in case of the latter, for which n?
finTwoZero : Fin 2
finTwoZero = zero
lemmaZeroIsNotOne : ¬ (finTwoZero ≡ suc zero)
lemmaZeroIsNotOne ()

-- Elements in different sublists should not be related.
testListRelat5 : ¬ (L ⊢ 4 ≈ 7)
testListRelat5 (p4 , p7 , m) = 
    let i4 = proj₁ p4 in
    let i7 = proj₁ p7 in
    let i4≡0 = lemmap4 p4 in
    let i7≡1 = lemmap7 p7 in
    let zeroIsI7 = trans (sym i4≡0) i4≡i7 in
    let zeroIsOne = trans zeroIsI7 i7≡1 in
    lemmaZeroIsNotOne zeroIsOne
        where
            i4≡i7 :  proj₁ p4 ≡ proj₁ p7
            i4≡i7 = m
