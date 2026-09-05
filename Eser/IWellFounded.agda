-- Module      : Eser.IWellFounded
-- Description : Well-foundedness for relations over indexed sets.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- Suppose you have a type `A : I → Set`
-- and a relation `_~_ : {i j : I} → A i → A j → Set` that doesn't really
-- care about the indices, and want to prove that it is well-founded.
-- Lifting its domain to `Σ[ i ∈ I ] A i` often doesn't work, because 
-- if x is a subterm of y, then (i , x) is not a subterm of (j , y).
-- So structural induction fails, even if x occurs in the constructor used by y.
--
-- The solution is to define more generalised versions of WellFoundedness
-- and accessibility and recursion principles,
-- that work with unions over all indices.
--
-- I made this file long ago. The last-modification was 25 May 2026
-- (it is August now by the time of writing).
--------------------------------------------------------------------------------
-- #TODO: Maybe contribute to stdlib?
-- #TODO: remark all is only proven for Set₀ but can probably be generalised.

open import Level
open import Data.Product
open import Induction.WellFounded
open import Induction
open import Relation.Binary.Construct.Closure.Transitive using (TransClosure)
    renaming (wellFounded to TransWellFounded)

module Eser.IWellFounded where

module IndexHeterogeneousTransClosure 
    {I : Set}
    {A : I → Set}
    where

    -- Generalisation of `TransClosure` from 
    -- Relation.Binary.Construct.Closure.Transitive
    -- to relations that are heretogeneous in the indices of the underlying
    -- type.
    --
    -- Don't confuse this with the "indexed relations"
    -- in the stdlib in Relation.Binary.Indexed.Homogeneous,
    -- There the related elements are of type `I → Set`, and `A ≗ I → Set`.
    -- In this file we have a very different situation:
    -- the base type instead is `A : I → Set`, so the related elements
    -- live in `A i`, each for some fixed `i`.
    data ITransClosure (_∼_ : {i j : I} → A i → A j → Set) 
                      : {i j : I} → A i → A j → Set where
        direct 
            : {i j : I} 
            → {a : A i} 
            → {b : A j} 
            → (a ∼ b) 
            → ITransClosure _∼_ a b
        composed --^ a∼b and b∼⁺c then a∼⁺c.
            : {i j k : I} 
            → {a : A i} 
            → {b : A j} 
            → {c : A k}
            → a ∼ b
            → ITransClosure _∼_ b c
            → ITransClosure _∼_ a c

    -- Predicate that an index-heterogeneous relation is transitive.
    ITransitive : (_∼_ : {i j : I} → A i → A j → Set) → Set
    ITransitive _∼_ = 
              {i j k : I}
            → {a : A i} 
            → {b : A j} 
            → {c : A k}
            → a ∼ b
            → b ∼ c
            → a ∼ c

    -- Theorem that the indexed-transitive-closure is actually transitive.
    ITransClosureTransitivity
        : (_∼_ : {i j : I} → A i → A j → Set) 
        → ITransitive (ITransClosure _∼_)
    ITransClosureTransitivity _∼_ {a = a} {b = b} {c = c} (direct a∼b) b∼⁺c 
        = composed a∼b b∼⁺c
    ITransClosureTransitivity _∼_ {a = a} {b = b} {c = c} 
        (composed {a = a} {b = z} {c = b} a∼z z∼⁺b) b∼⁺c = 
            let z∼⁺c = ITransClosureTransitivity _∼_ z∼⁺b b∼⁺c
            in
            composed a∼z z∼⁺c

    -- The predecessor-structure over the union of `_∼_ i j` 
    -- over all indices i and j.
    IWFRec : (_∼_ : {i j : I} → A i → A j → Set) 
           → RecStruct (Σ[ i ∈ I ](A i)) 0ℓ 0ℓ
    -- {i : I} (x : A i)
    IWFRec _∼_ P (i , x) = (j : I) → (y : A j) → y ∼ x → P (j , y)

open IndexHeterogeneousTransClosure

-- x : A i is accessible (from i) if all y s.t. y ∼ x are also accessible (from
-- j), for *any* index j s.t. y : A j.
data IAcc {I : Set} {A : I → Set} 
    (_∼_ : {i j : I} → A i → A j → Set) (i,x : Σ[ i ∈ I ](A i) ) : Set where
    iacc : (rs : IWFRec _∼_ (IAcc _∼_) i,x) → IAcc _∼_ i,x

IWellFounded : {I : Set} {A : I → Set} (_∼_ : {i j : I} → A i → A j → Set) → Set
IWellFounded {I} {A} _∼_ = {i : I} → (x : A i) → IAcc {I} {A} _∼_ (i , x)

-- Now we mimick Induction.WellFounded of the stdlib, but then for IWellFounded.
-- For the moment only for level 0ℓ, which is all I need.
module ISome {I : Set} {A : I → Set} {_∼_ : {i j : I} → A i → A j → Set} where
    iWFRecBuilder : SubsetRecursorBuilder (IAcc {I} {A} _∼_) (IWFRec _∼_)
    iWFRecBuilder P f x (iacc rs) j y y∼x = 
        -- * P is a predicate on Σ[i∈I](Ai).
        -- * f proves that `Rec P ⊆' P`, i.e., if Py for all y∼x then Px.
        -- The goal is to prove that (IAcc _∼_) ⊆' (Rec P),
        -- i.e., that if x is accessible then P holds for all y s.t. y∼x.
        -- By definition of accessibility of x, it follows from y∼x
        -- that also y is accessible.
        -- A recursive call on the accessibility of y (to iWFRecBuilder) 
        -- then proves that `Rec P y` holds, i.e, that Pz holds for all z∼y.
        let RecPY : (k : I) → (z : A k) → z ∼ y → P (k , z)
            RecPY = iWFRecBuilder P f (j , y) (rs j y y∼x)
        in
        -- We then input that to f to prove Py, which was to be shown.
        f (j , y) RecPY
        -- Why does the termination checker not complain?
        -- Because `rs` is a strictly smaller building block that `iacc rs`,
        -- and we are not applying rs to any function
        -- (instead we apply something TO rs, intuitively taking something out
        -- of it, instead of building something on top of it!)
    
    -- Now we get an induction principle that can be used to show a precidate P
    -- holds on all accessible elements. 
    -- Intuitively it requires showing 
    -- {i : I} → (x : A i) → ({j : I} → (y : A j) → y ∼ x → P y) → P x
    -- to conclude the 'P holds on all accessible elements':
    -- {i : I} → (x : A i) → Acc _∼_ x → P x.
    -- The actual implementation uses tuples
    -- Σ[ i ∈ I ](A i) instead of {i : I} → (x : A i).
    iWFRec : SubsetRecursor (IAcc {I} {A} _∼_) (IWFRec _∼_)
    iWFRec = subsetBuild iWFRecBuilder

-- As in the standard library, the previous induction principle can be
-- strengthened to *All points in Σ[ i ∈ I ](A i)* if all points are accessible.
-- Accessibility of all points (IWellFounded) is an argument to the module.
-- This is a fairly trivial corollary of ISome, which proves an induction
-- principle for "all accessible elements", which in this context are just all
-- elements.
module IAll 
    {I : Set} 
    {A : I → Set} 
    {_∼_ : {i j : I} → A i → A j → Set}
    (IWF : IWellFounded {I} {A} _∼_)
    where
    iWFRecBuilder : RecursorBuilder (IWFRec _∼_)
    iWFRecBuilder P f (i , x) = ISome.iWFRecBuilder P f (i , x) (IWF x) 
    --
    -- Now we get an induction principle that can be used to show a precidate P
    -- holds UNIVERSALLY.
    -- Intuitively it requires showing 
    -- {i : I} → (x : A i) → ({j : I} → (y : A j) → y ∼ x → P y) → P x
    -- to conclude the 'P holds on all elements':
    -- {i : I} → (x : A i) → P x.
    -- The actual implementation uses tuples
    -- Σ[ i ∈ I ](A i) instead of {i : I} → (x : A i).
    iWFRec : Recursor (IWFRec _∼_)
    iWFRec = build iWFRecBuilder

-- If x is accessible and y∼x then y is accessible.
elimIAcc
    : {I : Set} 
    → {A : I → Set} 
    → {_∼_ : {i j : I} → A i → A j → Set} 
    → {i : I}
    → {x : A i}
    → IAcc {I} {A} _∼_ (i , x)
    → {j : I}
    → {y : A j}
    → y ∼ x
    → IAcc {I} {A} _∼_ (j , y)
elimIAcc (iacc rs) {j = j} {y = y} y∼x = rs j y y∼x

-- If x is _∼_ accessible then x is also accessible in the transitive closure of
-- _∼_.
IAccImplIAccTransClosure
    : {I : Set} 
    → {A : I → Set} 
    → (_∼_ : {i j : I} → A i → A j → Set) 
    → {i : I}
    → (x : A i)
    → IAcc {I} {A} _∼_ (i , x)
    → IAcc {I} {A} (ITransClosure {I} {A} _∼_) (i , x)
IAccImplIAccTransClosure {I} {A} _∼_ {i} x (iacc rs) = iacc f
    where
        f 
            : (j : I) 
            → (y : A j)
            → ITransClosure {I} {A} _∼_ y x 
            → IAcc {I} {A} (ITransClosure {I} {A} _∼_) (j , y)
        f j y (direct y∼x) = 
            let yIAcc : IAcc {I} {A} _∼_ (j , y)
                yIAcc = rs j y y∼x
            in
            IAccImplIAccTransClosure _∼_ y yIAcc
        f j y (composed {j = k} {b = z} y∼z z∼⁺x) = 
            let zIAccTrans : IAcc {I} {A} (ITransClosure {I} {A} _∼_) (k , z)
                zIAccTrans = f k z z∼⁺x
            in
            let y∼⁺z : ITransClosure {I} {A} _∼_ y z
                y∼⁺z = direct y∼z
            in
            elimIAcc zIAccTrans y∼⁺z

-- The ITransClosure preserves IWell-Foundedness.
-- Obviously, since the definition of accessibility requires all
-- predecessors of x under the transitive closure to be accessible.
-- Hence accessibility of _«ₐ_ implies accessibility of _«+_.
ITransIWellFounded
    : {I : Set} 
    → {A : I → Set} 
    → (_∼_ : {i j : I} → A i → A j → Set) 
    → IWellFounded {I} {A} _∼_
    → IWellFounded {I} {A} (ITransClosure {I} {A} _∼_)
ITransIWellFounded {I} {A} _∼_ IWF {i} x 
    = IAccImplIAccTransClosure {I} {A} _∼_ {i} x (IWF x)

--------------------------------------------------------------------------------
-- Specialising to a specific index
--------------------------------------------------------------------------------
-- If _~_ is IAcc or IWellFounded then for any specific index i
-- the subrelation _~_ {i} {i} is WellFounded (in the non-indexed sense).
-- This was added in August 2026.
IAcc→Acc
    : {I : Set} 
    → {A : I → Set} 
    → {_∼_ : {i j : I} → A i → A j → Set}
    → (i : I)
    → (a : A i)
    → IAcc {I} {A} _∼_ (i , a)
    → Acc (_∼_ {i} {i}) a
IAcc→Acc {I} {A} {_∼_} i a (iacc f) = acc g
    where
        g : {b : A i} → (b ∼ a) → Acc (_∼_ {i} {i}) b
        g {b} b∼a = IAcc→Acc i b (f i b b∼a)

-- This is an easy corollary of IAcc→Acc.
IWF→WF
    : {I : Set} 
    → {A : I → Set} 
    → {_∼_ : {i j : I} → A i → A j → Set}
    → (IWF : IWellFounded {I} {A} _∼_)
    → (i : I)
    → WellFounded (_∼_ {i} {i})
IWF→WF IWF i a = IAcc→Acc i a (IWF a)
