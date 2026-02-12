-- Module      : StreamGrids.List
-- Description : Auxiliary functions for lists
-- Copyright   : (c) Lulof Pirée, 2025
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
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

open import Function.Base using (_∘_)
open import Data.List.Properties

open import StreamGrids.PropositionalEquality

module StreamGrids.List where

--------------------------------------------------------------------------------
-- Indicing in a List A.
--------------------------------------------------------------------------------
module SingleIndex 
    {ℓ : Level.Level}
    {A : Set ℓ}
    where

    Indices : List A → Set
    Indices L = Fin (length L)

    getEl : (L : List A) → Indices L → A
    getEl [] ()
    getEl (x ∷ xs) zero = x
    getEl (x ∷ xs) (suc i) = getEl (xs) i

    -- Left associative notation for indexing lists.
    -- So a list of lists can now be indexed as `L ,, i ,, j`.
    _,,_ : (L : List A) → Indices L → A
    L ,, i = getEl L i
    infixl 30 _,,_

    -- A proof of membership of an element is an index at which the element occurs.
    _∈_ : A → List A → Set ℓ
    a ∈ L = Σ[ i ∈ (Indices L) ]( L ,, i ≡ a)
    infixr 30 _∈_

    -- Get the index of an element of which we know it exists in the list.
    getListIdx : {L : List A} → {a : A} → (a ∈ L) → Indices L
    getListIdx {L} {a} (i , _) = i

open SingleIndex public

--------------------------------------------------------------------------------
-- Double-indiced lists (lists of lists)
--------------------------------------------------------------------------------
module DoubleIndex 
    {ℓ : Level.Level}
    {A : Set ℓ}
    where

    -- Predicate that says that an element occurs in at least one of the sublists.
    -- For example, it holds that:
    --      6 ∈∈ (( 1 ∷ 2 ∷ 3 ∷ [] ) ∷ ( 4 ∷ 5 ∷ 6 ∷ [] ) ∷ [])
    _∈∈_ : A → List (List A) → Set ℓ
    a ∈∈ L = Σ[ i ∈ (Indices L) ](
        Σ[ j ∈ (Indices (L ,, i)) ]( L ,, i ,, j ≡ a)
        )
    --^ In Python notation, this would be `L[i, j] = a`.
    infixr 30 _∈∈_

    -- Total number of elements in a doubly indexed list.
    flatLength : List (List A) → ℕ
    flatLength = length ∘ concat

    -- Get the index of the sublist of L that contains a,
    -- given that a occurs in some sublist.
    getSuperListIdx : {L : List(List A)} → {a : A} → (a ∈∈ L) → Indices L
    getSuperListIdx {L} {a} (i , _) = i

    -- This checks if x ≈ x' according to L, denoted as `L ⊢ x ≈ x'`,
    -- using the convention that x ≈ x' iff (x and x' are both in the same
    -- sublist of L).
    -- Warning: this is intended to be used in contexts 
    -- where x and x' occur in at most one sublist of L. 
    -- Otherwise x ≈ x' iff the FIRST sublists in which
    -- they occur are the same.
    listRelat : (L : List (List A)) → (x x' : A) → Set ℓ
    listRelat L x x' 
        = Σ[ p ∈ (x ∈∈ L) ]( 
          Σ[ q ∈ (x' ∈∈ L) ](
          (getSuperListIdx {L = L} {x} p) ≡ (getSuperListIdx {L = L} {x'} q)
        ))
    syntax listRelat L x x' = L ⊢ x ≈ x'

    -- Take out the first elements of nested lists.
    -- Ignore empty lists.
    -- E.g., [[1, 2, 3], [4, 5, 6], [], [7, 8, 9]] ↦  [1, 4, 7].
    firstElem : (L : List (List A)) → List A
    firstElem [] = []
    firstElem ([] ∷ Ls) = firstElem Ls
    firstElem ((a ∷ as) ∷ Ls) = a ∷ (firstElem Ls)

open DoubleIndex public

--------------------------------------------------------------------------------
-- Inserting elements in sublists of double-indexed lists.
-- Such inserts preserve a lot of properties of the original list.
--------------------------------------------------------------------------------

module DoubleInsert 
    {ℓ : Level.Level}
    {A : Set ℓ}
    where

    -- Insert a in the sublist L[i].
    -- Notation : `L [ i ]+= a`.
    insert 
        : (L : List (List A))
        → (a : A) 
        → (i : Indices L)
        → List( List A)
    insert L a i = L [ i ]%= λ as → a ∷ as
    infixl 5 insert
    syntax insert L a i = L [ i ]+= a

    insertPresvLength 
        : (L : List (List A))
        → (a : A) 
        → (i : Indices L)
        → length L ≡ length (L [ i ]+= a)
    insertPresvLength L a i = sym (length-%= L i (λ as → a ∷ as))

    insertPresvIndices
        : (L : List (List A))
        → (a : A) 
        → (i : Indices L)
        → Indices L ≡ Indices (L [ i ]+= a)
    insertPresvIndices L a i = cong (λ n → Fin n) (insertPresvLength L a i)

    insertIdxMap
        : (L : List (List A))
        → (a : A) 
        → (i k : Indices L)
        → Indices (L [ i ]+= a)
    insertIdxMap L a i k = coe (insertPresvIndices L a i) k

    insertPresvEl 
        : (L : List (List A))
        → (a : A) 
        → (i : Indices L)
        → {a' : A} 
        → a' ∈∈ L 
        → a' ∈∈ (L [ i ]+= a)
    insertPresvEl L a i {a'} (k , j , p) = 
        let p' = ? in
        let k' = insertIdxMap L a i k in
        (k' ,  {! inject₁ j !}  , p')

    lemma 
        : (L : List (List A))
        → (a : A) 
        → (i : Indices L)
        → {a' : A} 
        → (h : a' ∈∈ L)
        → (¬ ((proj₁ h) ≡ i))
        --^ a' is in sublist with index i
        → a' ∈∈ (L [ i ]+= a)
    lemma L a i {a'} (k , j , p) q = 
        let p' = ? in
        (k' ,  {! inject₁ j !}  , p')
        where
            L' : List (List A) 
            L' = L [ i ]+= a
            k' : Indices L'
            k' = insertIdxMap L a i k
            lenLi≡lenL'i : length (L ,, k) ≡ length ((L [ i ]+= a) ,, k')
            lenLi≡lenL'i = refl


open DoubleInsert public


--module DoubleInsert 
--    {ℓ : Level.Level}
--    {A : Set ℓ}
--    (L : List (List A))
--    --^ List to insert new element into.
--    (a : A) 
--    --^ Element to insert.
--    (i : Indices L)
--    --^ Index at which to insert a.
--    where



--open DoubleInsert public

----_[_]+=_ := insert


--The standard library has

--  ∈-∷=⁺-untouched : ∀ {xs x y v} (x∈xs : x ∈ xs) → (¬ x ≈ y) → y ∈ xs → y ∈ (x∈xs ∷= v)
--  ∈-∷=⁺-untouched (here  x≈z)  x≉y (here  y≈z)  = contradiction (trans x≈z (sym y≈z)) x≉y
--  ∈-∷=⁺-untouched (here  x≈z)  x≉y (there y∈xs) = there y∈xs
--  ∈-∷=⁺-untouched (there x∈xs) x≉y (here  y≈z)  = here y≈z
--  ∈-∷=⁺-untouched (there x∈xs) x≉y (there y∈xs) = there (∈-∷=⁺-untouched x∈xs x≉y y∈xs)
--in Data.List.Membership.Setoid.Properties
--That should deal with the indices that have not changed?
-- (1) It can (for List (List A) stuff) prove that the unchanged sublists are still in L';
-- these then obviously contain the elements the original sublist in L has.
-- (2) Now the stuff below should allow to prove that the extended sublist also has
-- all elements of the non-extended version.
-- So prove both of these things as a sublemma, then make a case distinction
-- on the first index of the element a' (like Tarmo suggested),
-- and all should work out -- in intuition...

--Data.List.Membership.Propositional.Properties has this:
--(not useful, only useful when using mappings of the form l' → x ∷ l'
--on the nested lists.
---- nested lists

--map∷⁻ : xs ∈ map (y ∷_) xss → ∃[ ys ] ys ∈ xss × xs ≡ y ∷ ys
--map∷⁻ = ∈-map⁻ (_ ∷_)

--[]∉map∷ : (List A ∋ []) ∉ map (x ∷_) xss
--[]∉map∷ p with () ← map∷⁻ p

--map∷-decomp∈ : (List A ∋ x ∷ xs) ∈ map (y ∷_) xss → x ≡ y × xs ∈ xss
--map∷-decomp∈ p with _ , xs∈xss , refl ← map∷⁻ p = refl , xs∈xss

--∈-map∷⁻ : xs ∈ map (x ∷_) xss → x ∈ xs
--∈-map∷⁻ p with _ , _ , refl ← map∷⁻ p = here refl

