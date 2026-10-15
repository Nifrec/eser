-- Module      : Eser.Filters.Composition
-- Description : Composing Filters and properties of composition.
-- Copyright   : (c) Lulof Pirée, 2026
-- License     : AGPL-v3
-- Maintainer  : Lulof Pirée
--------------------------------------------------------------------------------
-- Filter composition is NOT just pointwise ∧, as the ∧ of two dead-end-free
-- filters may very well have a dead end (i.e., be unsatisfiable, i.e., not
-- allowing *any choice* for some inputs).
--
-- However, we know that we can always take the congruence closure of a
-- relation. A relation R can be encoded as a filter F_R that allows only the
-- choices in R, so it is only satisfied by R.
-- We want to define a (non-symmetric) composition _»_ such that
-- F_R » P computes the P-closure of R (actually the filter that only allows
-- the relation that is the P-closure of R), where P is some dead-end-free
-- predicate like congruence.
--
-- We first adapt the definition of a Filter.
-- Instead of directly telling (via a Bool) for each choice of extending
-- an r : NFRestr n whether or not it is allowed, a Filter first tells whether
-- or not it 'fires' given r. If it fires, it behaves as usual.
-- If it doesn't fire (if it 'passes'), 
-- then we interpret that "every choice is OK, I don't care".
--
-- The composition G » F on input r returns (F r) : Choices r → Bool
-- if F fires on input r. If F passes on input r, but G fires on input r,
-- then we return (G r) : Choices r → Bool.
-- If both filters pass, then we accept all choices (so return (λ _ → true) :
-- Choices r → Bool).
--
-- This _»_ composition turns MayFireFilters into an idempotent non-commutative 
-- monoid, with the filter that always passes as unit.
-- The non-commutativity feels surprising, since combining predicates
-- on relations directly can be done via the commuting ∧,
-- but here the order does matter.
--
-- Note that passing is NOT the same as firing and then returning true on all
-- inputs, since passing goes to the next filter in the composition,
-- whereas firing gives a definite verdict on whether a choice is allowed.
-- Outside compositions, when the filter is used alone,
-- both options do behave identically though.
--------------------------------------------------------------------------------

--{-# OPTIONS --safe #-}
{-# OPTIONS --allow-unsolved-metas #-}

open import Data.Nat
open import Data.Bool hiding (_<_ ; _≤_)
open import Data.Empty
open import Data.Unit
open import Relation.Binary.PropositionalEquality
open ≡-Reasoning
open import Relation.Binary.Definitions 
    using (Tri ; Reflexive ; Symmetric ; Transitive ; DecidableEquality)
open Tri
open import Relation.Nullary
open import Data.Product
open import Data.Sum
open import Function using (_∘_ ; _$_)
open import Data.List using (List ; [] ; _∷_)
open import Data.List.Relation.Unary.Any as Any
open import Data.List.Relation.Unary.Any.Properties

open import Eser.EqRel.Definitions
open import Eser.EqRel.Conversions using (RelToFun)
open import Eser.EqRel.EqRelProperties
open import Eser.Aux using (_≈_ ; _↔_ ; ↔-to ; ↔-from)
open import Eser.Relation.Binary.Path

open import Eser.Filters.Conversions.NFFunToExence
open import Eser.Filters.Base
open import Eser.Filters.Properties
open import Eser.Filters.PointwiseProperties
open import Eser.Filters.Resurface

module Eser.Filters.Composition where

--------------------------------------------------------------------------------
-- MayFireFilters
--------------------------------------------------------------------------------

-- Functor isomorphic to 'Maybe', but I use a different name to avoid confusion
-- with Maybe's well-known monadic Kleisli composition (which is NOT _»_
-- composition!).
data MayFire (A : Set) : Set where
    fire : A → MayFire A
    pass : MayFire A

IsFire : {A : Set} → MayFire A → Set 
IsFire {A} m = Σ[ a ∈ A ] m ≡ fire a

IsPass : {A : Set} → MayFire A → Set
IsPass m = m ≡ pass

isfire? : {A : Set} (m : MayFire A) → Dec (IsFire m)
isfire? (fire a) = yes (a , refl)
isfire? pass = no λ ()

MayFireFilter : Set
MayFireFilter = 
      {n : ℕ}
    → (r : NFRestr n)
    → MayFire(Choices r → Bool)

MFF = MayFireFilter

-- How we interpret a MayFireFilter as a Filter: passing means allowing all
-- choices.
MFF→Filter : MayFireFilter → Filter
MFF→Filter F {n} r c = cases (F r) c
    where
        cases : MayFire (Choices r → Bool) → Choices r → Bool
        cases (fire f) c = f c
        cases pass _ = true

-- Always fire.
Filter→MFF : Filter → MayFireFilter
Filter→MFF F r = fire (F r)

--------------------------------------------------------------------------------
-- _»_ : MayFireFilter composition
--------------------------------------------------------------------------------
-- Right associativity: H » G » F ≔ H » (G » F). 
-- Not that it really matters since _×_ is associative anyway.
infixr 70 _»_

_»_ : MFF → MFF → MFF
(G » F) r = cases (F r)
    where   
        cases : MayFire (Choices r → Bool) → MayFire (Choices r → Bool)
        cases (fire f) = fire f
        cases pass = G r

-- _»_ is associative (up to function extensionality).
»-assoc : (H G F : MFF) → (H » G) » F ≈ H » (G » F)
»-assoc = {! TODO : Only prove if needed / if supervisors care. 
             Idem for units and unit laws. !}

--------------------------------------------------------------------------------
-- Filter encoding of a relation
--------------------------------------------------------------------------------

-- 'Same NFFun' up to function extensionality.
-- Defined as homotopy between underlaying ℕ → ℕ functions.
_≈'_ : NFFun → NFFun → Set
(g , _ , _) ≈' (f , _ , _) = g ≈ f

-- The imported _≡?_ from Filters.Properties gives 
-- decidable equality on NFS r for any r : NFRestr n.
-- But we also want to compare NFRestr themselves!
_≡NFRestr?_ : {n : ℕ} → DecidableEquality (NFRestr n)
r ≡NFRestr? s = ?


-- A Singleton Filter is a filter that is satisfied by exactly one relation.
IsSingleton : Filter → Set
IsSingleton F = 
    Σ[ f ∈ NFFun ] (NFFun-sats F f) × ((g : NFFun) → NFFun-sats F g → g ≈' f)

IsSingleton' : MFF → Set
IsSingleton' = IsSingleton ∘ MFF→Filter

--------------------------------------------------------------------------------
-- Definition of P-closure of a relation given a predicate P
--------------------------------------------------------------------------------
-- In set theory it is easy, the P-closure of R is the smallest extension of
-- R that makes it satisfy P.
--
-- It particular, it is the relation R' such that 
-- 1. R ⊆ R'
-- 2. R' satisfies P
-- 3. For all S with R ⊆ S that satisfy P, we have R' ⊆ S.
--
-- This does not exist for all predicates P.
-- For example, if P says "has at least 3 equivalence classes",
-- and R has 2 of them, then there is no extension of R with more than 2
-- equivalence classes (indeed, any new arrow between two elements not yet in R
-- would only collapse the two equivalence classes into one!).
--
-- We formalise the classical definition of the closure,
-- and then characterise the filter-implemented-predicates that are closable.
-- This also comes with an algorithm to 
-- actually compute the closure of a relation.
--
-- In particular, a filter P is a closable predicate if and only if P is
-- 1. One-hot (if it fires, it allows exactly one choice).
-- 2. Dead-end-free.
-- 3. Never forces the unique choice when firing to be newNF.
--
-- The P-closure of a relation R is then simply the unique relation
-- satisfying the singleton filter F_R » P
-- where F_R = Filter→MFF (NFFun→Filter R).
-- (That that is a singleton does require a lemma).

-- #QUESTION : define this in terms of EqRel or NFFuns?
-- Currently using EqRel since the definition is quite extensional,
-- from an NFFun one cannot immediately tell which elements are related.
-- One can by converting the NFFun to an EqRel or by (1) converting it to an
-- Exence and 
-- (2) using the AreRelated defined in Eser.Filters.NormalityInNFRestr.
Rel-sats' : MFF → EqRel → Set
Rel-sats' = Rel-sats ∘ MFF→Filter
Exence-sats' : MFF → Exence → Set
Exence-sats' = Exence-sats ∘ MFF→Filter

record _closure-of_ (F : Filter) (R : EqRel) : Set
    where
        field
            rel : EqRel
            ext : R ⊆ rel
            sat : Rel-sats F rel
            min : ((S : EqRel) → R ⊆ S → Rel-sats F S → rel ⊆ S)
open _closure-of_

_closure-of'_ : MFF → EqRel → Set
_closure-of'_ = _closure-of_ ∘ MFF→Filter

-- Extensional equality between relations: 
-- homotopy between the underlying ℕ → ℕ → Bool functions.
_≣_ : EqRel → EqRel → Set
(R , _) ≣ (S , _) = R ≈ S

-- Predicate that a relation is (extensionally) equal to the F-closure of R.
_is-the_closure-of_ : EqRel → MFF → EqRel → Set
S is-the F closure-of R = Σ[ C ∈ F closure-of' R ] (S ≣ rel C)

--------------------------------------------------------------------------------
-- Uniqueness of P-closure
--------------------------------------------------------------------------------
-- The definition of a closure of a relation already implies it is
-- unique, at least up to function extensionality.
 

⊆→⊆→≣ : {R S : EqRel} → R ⊆ S → S ⊆ R → R ≣ S
⊆→⊆→≣ = ?

closure-unique
    : {P : Filter}
    → {R : EqRel}
    → (R' S' : P closure-of R)
    → (rel R') ≣ (rel S')
closure-unique = {! #TODO: use the third property of closure-of, 
    both on R and S, to get R ⊆ S and S ⊆ R, conclude by ⊆→⊆→≣ !}


--------------------------------------------------------------------------------
-- Charactersisation of closable filters
--------------------------------------------------------------------------------

IsClosable : Filter → Set
IsClosable F = (R : EqRel) → F closure-of R

IsClosable' : MFF → Set
IsClosable' F = (R : EqRel) → (MFF→Filter F) closure-of R

DeadEndFree' : MFF → Set
DeadEndFree' = DeadEndFree ∘ MFF→Filter

-- Filters that allow exaclty one choice when they fire.
OneHotFilter : Set
OneHotFilter = {n : ℕ} → (r : NFRestr n) → MayFire (Choices r)

OneHot→MFF : OneHotFilter → MFF
OneHot→MFF F' r = cases (F' r)
    module OneHotToMFFImpl where
        cases : MayFire (Choices r) → MayFire (Choices r → Bool)
        cases pass = pass
        cases (fire c) = fire $ λ c' → does (c ≡? c')

OneHot→Filter : OneHotFilter → Filter
OneHot→Filter = MFF→Filter ∘ OneHot→MFF

-- #QUESTION: could also define as 
-- IsOneHot F = Σ[ F' ∈ OneHotFilter ] F ≈ (OneHot→Filter F')
-- Would that be better?
-- #QUESTION: or remove the definition of 'OneHotFilter' alltogether?
IsOneHot : Filter → Set
IsOneHot F = 
      {n : ℕ} 
    → (r : NFRestr n) 
    → {c c' : Choices r} 
    → F allows c to r 
    → F allows c' to r 
    → c ≡ c'

IsOneHot' : MFF → Set
IsOneHot' = IsOneHot ∘ MFF→Filter

-- Sanity check of definition 'OneHotFilter'.
OneHot→IsOneHot : (F : OneHotFilter) → IsOneHot (OneHot→Filter F)
OneHot→IsOneHot = ?

NeverForcesnewNF : Filter → Set
NeverForcesnewNF F = 
      {n : ℕ} 
    → (r : NFRestr n) 
    → (c : Choices r)
    → F allows c to r
    → c ≢ here

NeverForcesnewNF' : MFF → Set
NeverForcesnewNF' = NeverForcesnewNF ∘ MFF→Filter

-- Big theorem: characterisation of closable predicates (expressed as a filter).
-- #QUESTION: maybe better define this for Filter rather than MFF
-- and get the special case for MFF as a cheap corollary?
-- #ANSWER: no ofc not. A 'Filter' always fires. If it 
-- always fires, and never chooses newNF, then it just forces the full relation,
-- i.e., relating everything to 0. This characterisation is only useful for
-- MayFireFilters!
closable-characterisation'
    : (F : MFF)
    → (IsClosable' F) ↔ (DeadEndFree' F × IsOneHot' F × NeverForcesnewNF' F)
closable-characterisation' = ?

allows'-to
    : (F : MFF)
    → {n : ℕ}
    → (r : NFRestr n)
    → Choices r
    → Set
allows'-to F r c = (MFF→Filter F) allows c to r

syntax allows'-to F r c = F allows' c to r

-- 𝐂𝐨𝐫𝐨𝐥𝐥𝐚𝐫𝐲
-- Any closable filter that always fires allows exactly one choice
-- in each NFRestr.

AlwaysFires : MFF → Set
AlwaysFires F = {n : ℕ} → (r : NFRestr n) → IsFire (F r)


get-unique-choice
    : {F : MFF}
    → IsClosable' F
    → AlwaysFires F
    → {n : ℕ}
    → (r : NFRestr n)
    → Σ[ c ∈ Choices r ] (F allows' c to r) 
                       × ((c' : Choices r) → (F allows' c' to r) → (c' ≡ c))
get-unique-choice {F} C AF r = 
    let (def , oh , nonewNF) = ↔-to (closable-characterisation' F) C
    in
    ?
    

--------------------------------------------------------------------------------
-- Corollary : compositions of closable filters remain closable
--------------------------------------------------------------------------------

deadendfree-compos
    : {F G : MFF}
    → DeadEndFree' F
    → DeadEndFree' G
    → DeadEndFree' (G » F)
deadendfree-compos = ?

onehot-compos
    : {F G : MFF}
    → IsOneHot' F
    → IsOneHot' G
    → IsOneHot' (G » F)
onehot-compos = ?

neverforcesnewnf-compos
    : {F G : MFF}
    → NeverForcesnewNF' F
    → NeverForcesnewNF' G
    → NeverForcesnewNF' (G » F)
neverforcesnewnf-compos = ?

closable-compos
    : {F G : MFF}
    → IsClosable' F
    → IsClosable' G
    → IsClosable' (G » F)
closable-compos = {! 
    #TODO: duh, they remain dead-end-free, 
    they remain NeverForcesnewNF, and they
    remain one-hot. 
    So it follows easily from the characterisation theorem.
    !}

--------------------------------------------------------------------------------
-- Lemma : P-closures of relations satisfying a filter
--------------------------------------------------------------------------------

-- If a relation R satisfies F, then the P-closure R' of R satisfies F » P.
-- (Note: the reverse implication does not hold. E.g., take F ≔ P,
-- then R' obviously satisfies P » P, but R may not satisfy P).
closure-sat-preservation
    : {F P : MFF}
    → {R : EqRel}
    → IsClosable' P
    → Rel-sats' F R
    → (R' : P closure-of' R)
    → Rel-sats' (F » P) (rel R')
closure-sat-preservation = ?

--------------------------------------------------------------------------------
-- A composition of dead-end-free one-hot MFFs is a singleton
-- as soon as any of the composites is.
--------------------------------------------------------------------------------
-- This follows induction on the composition, using these two lemmas:

compo-singleton-left
    : {F G : MFF}
    → DeadEndFree' F
    → DeadEndFree' G
    → IsOneHot' F
    → IsOneHot' G
    → IsSingleton' G
    → IsSingleton' (G » F)
compo-singleton-left = ?

compo-singleton-right
    : {F G : MFF}
    → DeadEndFree' F
    → DeadEndFree' G
    → IsOneHot' F
    → IsOneHot' G
    → IsSingleton' G
    → IsSingleton' (G » F)
compo-singleton-right = ?

--------------------------------------------------------------------------------
-- Other properties of composition and MFFs
--------------------------------------------------------------------------------
-- These may be moved to earlier in the file, as other lemmas depend on them.

singleton→alwaysfires : {F : MFF} → IsSingleton' F → AlwaysFires F
singleton→alwaysfires = ?

singleton→onehot : {F : MFF} → IsSingleton' F → IsOneHot' F
singleton→onehot = ? 

singleton→deadendfree : {F : Filter} → IsSingleton F → DeadEndFree F
singleton→deadendfree = ?

singleton→deadendfree' : {F : MFF} → IsSingleton' F → DeadEndFree' F
singleton→deadendfree' {F} = singleton→deadendfree {MFF→Filter F}


onehot×alwaysfires↔singleton
        : (F : MFF)
        → (IsOneHot' F × AlwaysFires F) ↔ (IsSingleton' F)
onehot×alwaysfires↔singleton = ?

--------------------------------------------------------------------------------
-- Extender composition
--------------------------------------------------------------------------------
-- Main idea: given equations E1, E2, E3, ... which you want to add to a
-- relation R, one can close R by E1, then the result by E2, then that result by
-- E3, and so on, and end by closing with congruence.
--
-- Note that 'Taking the closure of _' is an operation EqRel → EqRel
-- s.t. the output is an extension of the input. We can generalise this:
Extender : Set
Extender = (R : EqRel) → Σ[ S ∈ EqRel ] R ⊆ S

⊆-trans : {R S T : EqRel} → R ⊆ S → S ⊆ T → R ⊆ T
⊆-trans R⊆S S⊆T x y = (S⊆T x y) ∘ (R⊆S x y)

-- Extender composition. G ⋗ F means: first extend with F, then extend the
-- result with G.
infixr 50 _⋗_
_⋗_ : Extender → Extender → Extender
(G ⋗ F) R = 
    let (R' , R⊆R') = F R in
    let (R'' ,  R'⊆R'') = G R' in
    (R'' , ⊆-trans {R} {R'} {R''} R⊆R' R'⊆R'')

IsClosable→Extender 
    : {F : Filter}
    → IsClosable F
    → Extender
IsClosable→Extender {F} close R = (rel (close R) , ext (close R))


--------------------------------------------------------------------------------
-- Equality filters
--------------------------------------------------------------------------------
-- In practice, many filters have a simple structure.
-- They want to enforce the equation `n ≡ m` where m < n.
-- That comes down to forcing the choice of n to be the normal form of m.
-- This is a simple structure, because it doesn't really depend on the earlier
-- choices in the input NFRestr. Constrast this with the congruence 
-- or has-at-most-2-equivalence-classes filters, which do need to inspect the
-- structure of existing equivalence classes.
--
-- The main advantage of such 'equation filters' is that they are all closable
-- and that, when closing w.r.t. multiple equation filters, their order doesn't
-- matter (_⋗_ becomes commutative). This makes it easy to construct the closure
-- w.r.t. your set of equations!
--
-- Equation filters are allowed to have countably many equations,
-- but at most one for each RHS. I take the convention that the RHS of an
-- equation is larger than the LHS. (Equations where both sides are equal are
-- useless, since all equivalence relations are already reflexive anyway).

SingleEq : Set
SingleEq = Σ[ n ∈ ℕ ] Σ[ m ∈ ℕ ] m < n

EqFilter : Set
EqFilter = (n : ℕ) → MayFire( Σ[ m ∈ ℕ ] m < n )

SingleEq→EqFilter : SingleEq → EqFilter
SingleEq→EqFilter (n , m , m<n) k = cases (n Data.Nat.≟ k)
    where
        cases : Dec (n ≡ k) → MayFire ( Σ[ m ∈ ℕ ] m < k )
        cases (no _) = pass
        cases (yes refl) = fire (m , m<n)

EqFilter→OneHot : EqFilter → OneHotFilter
EqFilter→OneHot E {n} r = cases (E n)
    module EqFilterToOneHotImpl where
        cases : MayFire ( Σ[ m ∈ ℕ ] m < n ) → MayFire (Choices r)
        cases pass = pass
        cases (fire (m , m<n)) = fire $ earlier-new $ resurface r m<n

EqFilter→MFF : EqFilter → MFF
EqFilter→MFF = OneHot→MFF ∘ EqFilter→OneHot

EqFilter→Filter : EqFilter → Filter
EqFilter→Filter = MFF→Filter ∘ EqFilter→MFF

EqFilter-NeverForcesnewNF
    : (E : EqFilter)
    → NeverForcesnewNF' (EqFilter→MFF E)
EqFilter-NeverForcesnewNF E = ?

EqFilter-IsClosable'
    : (E : EqFilter)
    → IsClosable' (EqFilter→MFF E)
EqFilter-IsClosable' E = ?

EqFilter-IsClosable
    : (E : EqFilter)
    → IsClosable (EqFilter→Filter E)
EqFilter-IsClosable E = ?

infix 100 ∗_
∗_ : EqFilter → Extender
∗_ = IsClosable→Extender ∘ EqFilter-IsClosable 

Eq : EqFilter → ℕ → ℕ → Set
Eq E x y = Σ[ x<y ∈ (x < y) ] E y ≡ fire (x , x<y)

eqfilter-closure-subrelat
    : {E : EqFilter}
    → {R : EqRel}
    → {x y : ℕ}
    → Eq E x y
    → (proj₁ $ (∗ E) R) relates x to y
eqfilter-closure-subrelat {E} {R} {x} {y} xEy = ?

--------------------------------------------------------------------------------
-- Turning an NFFun into a filter that is only satisfied by that NFFun.
--------------------------------------------------------------------------------

-- We cannot turn an NFFun into an EqFilter, since the output
-- on input n should be (f n , f n < n), but it is possible that f n ≡ n.
-- However, since f n ≤ n, we do have enough information to construct a
-- OneHotFilter: in case that f n ≡ n, we can pick the choice `here`.
NFFun→OneHot : NFFun → OneHotFilter
NFFun→OneHot (f , f-leq , f-fix) {n} r = fire c
    where
        c : Choices r
        -- This is `here` if f n ≡ n,
        -- and (earlier-new $ resurface m<n) if f n ≡ m for some m < n.
        c = resurface' r (f-leq n)

NFFun→Filter : NFFun → Filter
NFFun→Filter = OneHot→Filter ∘ NFFun→OneHot

NFFun→MFF : NFFun → MFF
NFFun→MFF = OneHot→MFF ∘ NFFun→OneHot

EqRel→MFF : EqRel → MFF
EqRel→MFF = NFFun→MFF ∘ RelToFun

EqRel→Filter : EqRel → Filter
EqRel→Filter = NFFun→Filter ∘ RelToFun

--NFFun→Filter-self-sats
--    : (f' : NFFun)
--    → NFFun-sats (NFFun→Filter f') f'
--NFFun→Filter-self-sats f' = ?

--NFFun→Filter-singleton
--    : (f' : NFFun)
--    → IsSingleton (NFFun→Filter f')
--NFFun→Filter-singleton = ?

--NFFun→Filter-deadendfree
--    : (f' : NFFun)
--    → DeadEndFree (NFFun→Filter f')
--NFFun→Filter-deadendfree = ?

-- The only NFFun that satisfies `NFFun→Filter f` is `f` itself (up to function
-- extensionality).
-- This is the specification of `NFFun→Filter`, so this lemma proves
-- the correctness of `NFFun→Filter`.
NFFun→Filter-unique-sat
    : (f' g' : NFFun)
    → NFFun-sats (NFFun→Filter f') g'
    → g' ≈' f'
NFFun→Filter-unique-sat = {! #TODO: Should be corollary of the above two lemmas !}


id-Extender : Extender
id-Extender R = (R , ⊆-refl R)

eq-list-closure : List EqFilter → Extender
eq-list-closure [] = id-Extender
eq-list-closure (E ∷ Es) = ∗ E ⋗ (eq-list-closure Es)

remove? : Set
remove? = {! Next def and two lemmas below are unused? I commented them out for now. !}
--_fires-with_ 
--    : (P : MFF)
--    → {y : ℕ}
--    → Σ[ r ∈ NFRestr y ] Choices r
--    → Set
--P fires-with (r , c) = cases (P r)
--    where
--        cases : MayFire (Choices r → Bool) → Set
--        cases pass = ⊥
--        cases (fire f) = f c ≡ true

--IsClosable'→LocallyOneHot
--    : {P : MFF}
--    → IsClosable' P
--    → {n : ℕ}
--    → {r : NFRestr n}
--    → (c : Choices r)
--    → P fires-with (r , c)
--    → LocallyOneHot (MFF→Filter P) r c
--IsClosable'→LocallyOneHot = ?

---- Let P be a closable filter (so it is one-hot) and S be the P-closure of R.
---- Then if x is the unique choice that P (S ↾ y) allows, then xSy holds.
--closure-contains-required-equations
--    : {P : MFF}
--    → {R S : EqRel}
--    → (C : IsClosable' P)
--    → S ≡ rel (C R)                 --^ S is only needed for readability.
--    → {y : ℕ}
--    → (c : Choices (S ↾ y))
--    → P fires-with (S ↾ y , c)
--    → S relates y to (choiceToℕ c)
--closure-contains-required-equations {P} {R} {S} C refl {y} c P-fires-c = 
--    unique-choice-to-relate {MFF→Filter P} {S} {y} c loconehot
--    where
--        r : NFRestr y
--        r = S ↾ y
--        loconehot : LocallyOneHot (MFF→Filter P) r c
--        loconehot = IsClosable'→LocallyOneHot {P} C c P-fires-c

--------------------------------------------------------------------------------
-- Further notes
--------------------------------------------------------------------------------
-- Maybe the following obervations are worth formalising, maybe not.
-- At least they are important examples for intuition about the usage and limits
-- of filters. Especially useful to mention in a remark when writing a paper.

-- The "has at most 3 equivalence classes" filter is expressible,
-- non trivial and not one-hot. This shows not all usefull filters are
-- necessarily one-hot. (Also works for other numbers than 3, of course).

-- The "has at least 1+n equivalence classes" predicate
-- cannot be expressed as a filter. 

--------------------------------------------------------------------------------
-- Finitely presentable signature quotients
--------------------------------------------------------------------------------

todo-forsigna : Set
todo-forsigna = {! dont forget: prove correctness for signature; add congr 
                   to the composition, then prove the output 
                   (1) has all the equations in it.
                   (2) it is closed under congruence.
                   ...
                   Not sure how to state concisely that 
                   it doesn't have anything else.!}

todo-catstuff : Set
todo-catstuff = {! dont forget: initial σ-algebra respecting R !}


--------------------------------------------------------------------------------
-- Next steps
-- #TODO: these are already outdated. Need to be updated using EqFilters
-- etc.
--------------------------------------------------------------------------------
-- 1. Define 'swap' as a eqfilter filter on replacement structures.
-- 2. Define finite multisets by quotienting List ℕ.
-- 4. Correct-by-construction representation or other tool for building such
--    sets of equations.
-- 5. Binay associativity filter, show it is closable.
-- 6. Use 3., 4. and 5. to give a toolbox for building decidable finitely
--    presented monoids.


--------------------------------------------------------------------------------
-- Don't forgets
--------------------------------------------------------------------------------
-- * Example of expressivity: 'at most 2 equiv classes'.
-- * Example non-expressivity: 'at least 3 equiv classes'.

don'tforget : Set
don'tforget = {! TODO: don't forget !}

