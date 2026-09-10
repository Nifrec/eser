-- Module      : Eser.NormVel
-- Description : Vectors as functions but with extensionality principle.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- Consider trees with arbitrary many children:
-- data Tree : Set where
--     node : {n : ℕ} → Vec Tree n → Tree
-- 
-- Then one cannot simply recurse on its children.
-- E.g. the termination checker rejects the following:
-- height : Tree → ℕ
-- height (node {n} v) = 1 + max (map height v)
--
-- One solution is to use `Vector Tree n` (which is `Fin n → Tree`)
-- instead of `Vec Tree n`.
-- However, without function extensionality, 
-- this makes extensionality equal trees not always propositionally equal.
--
-- Giving children one-by-one is an option:
-- data Tree : Set where
--     new : Tree
--     add-child : Tree → Tree → Tree
-- But my supervisor does not like this for some reason.
-- Well, it does make proofs and functions more complex.
--
-- So all these tree options fail, this module presents a fourth solution:
-- NVec: normalised Vectors.
--------------------------------------------------------------------------------
open import Data.Nat
open import Data.Product
open import Relation.Nullary
open import Relation.Binary
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning 
open import Data.Vec.Functional 
open import Data.Vec.Functional.Properties
open import Data.Vec.Properties using (tabulate-cong)
open import Data.Fin using (Fin)
open import Function hiding (_↔_)

open import Eser.Aux

module Eser.NormVec where

NVec : (A : Set) → ℕ → Set
NVec A n = Σ[ v ∈ Vector A n ] v ≡ (fromVec (toVec v))

-- Make an NVec from a Vector.
-- ("normalise" the Vector).
norm : {A : Set} → {n : ℕ} → Vector A n → NVec A n
norm v = (fromVec (toVec v) , eq)
    where
        eq : (fromVec $ toVec v) ≡ (fromVec $ toVec $ fromVec $ toVec v)
        eq = cong (λ x → fromVec x) (sym $ toVec∘fromVec (toVec v))

-- Lookup an element (Haskell-style notation).
infixl 30 _!!_
_!!_ : {A : Set} → {n : ℕ} → NVec A n → Fin n → A
_!!_ (v , _) i = v i

--------------------------------------------------------------------------------
-- Extensionality principle for NVecs
--------------------------------------------------------------------------------
toVec-lemma
    : {A : Set}
    → {n : ℕ}
    → (v w : Vector A n)
    → v ≈ w
    → toVec v ≡ toVec w
toVec-lemma v w H = tabulate-cong H

NVec-ex 
    : {A : Set}
    → {n : ℕ}
    → (v w : NVec A n)
    → ((i : Fin n) → v !! i ≡ w !! i)
    → v ≡ w
NVec-ex {A} {n} (v , p) (w , q) v≈w = restIsProofIrrel irrel p q v≡w
    where
        irrel 
            : (x : Vector A n) 
            → Relation.Nullary.Irrelevant (x ≡ fromVec (toVec x))
        irrel x p q = uip p q
        v≡w : v ≡ w
        v≡w =
            begin 
                v
            ≡⟨ p ⟩
                fromVec (toVec v)
            ≡⟨ cong fromVec $ toVec-lemma v w v≈w ⟩
                fromVec (toVec w)
            ≡⟨ sym q ⟩
                w
            ∎
            

--------------------------------------------------------------------------------
-- Test that the termination checker is OK with recursion.
--------------------------------------------------------------------------------

data Tree : Set where
    node : {n : ℕ} → NVec Tree n → Tree

height : Tree → ℕ
height (node {n} (v , p)) = 1 + max v'
    where
        v' : Vector ℕ n
        v' i = height $ v i
        max : Vector ℕ n → ℕ
        max = foldr _⊔_ 0

-- Tree with 1 childless node.
leaf : Tree
leaf = node $ norm v
    where
        v : Vector Tree 0
        v ()
        
-- Three with 3 nodes.
3-tree : Tree
3-tree = node $ norm v
    where
        v : Vector Tree 2
        v _ = leaf

5-tree : Tree
5-tree = node $ norm v
    where
        v : Vector Tree 3
        v Fin.zero = leaf
        v (Fin.suc Fin.zero) = 3-tree
        v (Fin.suc (Fin.suc Fin.zero)) = leaf

leaf-test : height leaf ≡ 1
leaf-test = refl
3-test : height 3-tree ≡ 2
3-test = refl
5-test : height 5-tree ≡ 3
5-test = refl
