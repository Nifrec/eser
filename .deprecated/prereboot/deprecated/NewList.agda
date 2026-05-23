-- Copyright   : (c) Lulof Pirée, 2025
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
-- Stability   : experimental
--------------------------------------------------------------------------------
-- TODO: probably not all of these are needed.

--open import Data.Bool hiding (_≤_; _≤?_)
--open import Data.Empty
--open import Data.Fin hiding (_<_)
--open import Function using (Inverseᵇ)
--open import Data.Nat hiding (_<_)
--open import Data.Nat.Properties
--open import Data.Sum
--open import Relation.Binary.Core using (Rel)
--open import Relation.Binary.Definitions
--open import Relation.Binary.PropositionalEquality hiding ([_])
--open import Function.Base using (_∘_)
--open import Data.Unit

open import Level
open import Data.Product
open import Relation.Nullary
open import Data.List
open import Data.List.Membership.Propositional
open import Data.List.Membership.Propositional.Properties
open import Data.List.Properties
open import Data.Fin
open import Data.List.Relation.Unary.Any using (Any)
    renaming (lookup to Any-lookup)
open import Relation.Binary.PropositionalEquality hiding ([_])

open import StreamGrids.PropositionalEquality

module StreamGrids.NewList where
    
-- Generic definitions for all lists.
module _ {A : Set _} where
    Indices : List A → Set _
    Indices L = Fin (length L)

    -- Left associative notation for indexing lists.
    -- So a list of lists can now be indexed as `L ,, i ,, j`.
    _,,_ : (L : List A) → Indices L → A
    L ,, i = lookup L i
    infixl 30 _,,_

-- Module concerning lists of lists.
module DoubleIndex {A : Set _} where

    -- x ∈∈ xss denotes that x is a member of some lowlist xs ∈ xss. 
    -- Intuitively: x ∈ xs ∈ xss.
    infix 4 _∈∈_ _∉∉_

    _∈∈_ : A → List (List A) → Set _
    a ∈∈ L = Σ[ i ∈ (Indices L) ](
        Σ[ j ∈ (Indices (L ,, i)) ]( L ,, i ,, j ≡ a)
        )
    --^ In Python notation, this would be `L[i, j] = a`.
    -- Alternative implementation:
    --      x ∈∈ xss = Any (λ xs → x ∈ xs) xss
    -- This version gives less readable terms.

    _∉∉_ : A → List (List A) → Set _
    x ∉∉ xss = ¬ (x ∈∈ xss)

    -- Insert an element in a lowlist by pointing to the lowlist directly.
    insertLow
        : {xss : List (List A)}
        → {xs : List A}
        → (x : A) 
        → (xs∈xss : xs ∈ xss)
        → List( List A )
    insertLow {xss} {xs} x xs∈xss = xs∈xss ∷= (x ∷ xs)

    --infixl 5 insertLow
    --syntax insertLow x xs∈xss = [ xs∈xss ]+= x

    -- Insert an element in a lowlist by pointing to the *index of* the lowlist.
    -- Implementation detail: xss could be implicit, but `i : Indices xss`
    -- could be an index of any list with the same length, 
    -- so Agda would probably fail to determine `xss` automatically anyway.
    insertIdx
        : (xss : List (List A))
        → (x : A) 
        → (i : Indices xss)
        → List( List A )
    insertIdx xss x i = xss [ i ]∷= (x ∷ xs)
        where
            xs = lookup xss i
        --let xs∈xss =  Data.List.Membership.Propositional.Properties.∈-lookup i in 
        --insertLow {xss} x xs∈xss

    infixl 5 insertIdx
    syntax insertIdx xss x i = xss [ i ]+= x

    insertPresvLength 
        : (xss : List (List A))
        → (x : A) 
        → (i : Indices xss)
        → length xss ≡ length (xss [ i ]+= x)
    insertPresvLength xss  x i = sym (length-∷= xss i (x ∷ xs))
        where
            xs = lookup xss i

    insertPresvIndices
        : (xss : List (List A))
        → (x : A) 
        → (i : Indices xss)
        → Indices xss ≡ Indices (xss [ i ]+= x)
    insertPresvIndices xss x i = cong (λ n → Fin n) (insertPresvLength xss x i)

    lemma
        : (xs : List A)
        → (x : A) 
        → (a : A)
        → a ∈ xs
        → a ∈ (x ∷ xs)
    lemma xs x a a∈xs = ?

    -- All existing elements are preserved when adding an element to a lowlist.
    insertPresvEl
        : (xss : List (List A))
        → (x : A) 
        → (i : Indices xss)
        → {a : A}
        → a ∈∈ xss
        → a ∈∈ (xss [ i ]+= x)
    insertPresvEl xss x i {a} (i' , j , xss[i',j]≡a ) with i ≟ i'
    ... | yes i≡i' = {! lemma (xss ,, i') x a!}? -- with <j is last idx, then a = x> = {! (i' , j , ?) !}
    ... | no p = ?

--insertPresvEl 
--    : (L : List (List A))
--    → (a : A) 
--    → (i : Indices L)
--    → {a' : A} 
--    → a' ∈∈ L 
--    → a' ∈∈ (L [ i ]+= a)
--insertPresvEl L a i {a'} (k , j , p) = 
--    let p' = ? in
--    let k' = insertIdxMap L a i k in
--    (k' ,  {! inject₁ j !}  , p')
-- Data.List.Membership.Setoid has the following conversion from indices to _∈_
-- proofs:
--module _ (S : Setoid c ℓ) where

--  open Setoid S using (refl)
--  open Membership S using (_∈_)

--  ∈-lookup : ∀ xs i → lookup xs i ∈ xs
--  ∈-lookup (x ∷ xs) zero    = here refl
--  ∈-lookup (x ∷ xs) (suc i) = there (∈-lookup xs i)


--insertIdxMap
--    : (L : List (List A))
--    → (a : A) 
--    → (i k : Indices L)
--    → Indices (L [ i ]+= a)
--insertIdxMap L a i k = coe (insertPresvIndices L a i) k


--------------------------------------------------------------------------------
-- Deprecated stuff
--------------------------------------------------------------------------------

-- Relation.Binary.PropositionalEquality.setoid does already exactly this:

---- Default way of seeing a set of terms as a Setoid, 
---- using propositional equality as the equivalence relation.
--toSetoid : (A : Set _) → Setoid _ _
--toSetoid A = record {Carrier = A ; _≈_ = _≡_ ; isEquivalence = isEquivalence}
--open DoubleIndex public

{-
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
-}
