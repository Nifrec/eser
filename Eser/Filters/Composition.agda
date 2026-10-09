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

{-# OPTIONS --safe #-}

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

--open import Data.Nat.Properties using 
--    (m<1+n⇒m<n∨m≡n 
--    ; n<1+n 
--    ; <-irrefl 
--    ; m≤n⇒m<n∨m≡n
--    ; <-trans
--    ; n≮n
--    ; <-irrelevant
--    ; suc-injective
--    ; ≤-refl
--    ; ≤-trans
--    ; n≤1+n
--    ; ≤-<-trans
--    )

open import Eser.EqRel.Definitions using (NFFun) renaming (DecEquiv to EqRel)
open import Eser.EqRel.Conversions using (RelToFun)
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
IsFire (fire _) = ⊤
IsFire pass = ⊥

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
_≈≈_ : NFFun → NFFun → Set
(g , _ , _) ≈≈ (f , _ , _) = g ≈ f

-- The imported _≡?_ from Filters.Properties gives 
-- decidable equality on NFS r for any r : NFRestr n.
-- But we also want to compare NFRestr themselves!
_≡NFRestr?_ : {n : ℕ} → DecidableEquality (NFRestr n)
r ≡NFRestr? s = ?

filterify : NFFun → Filter
filterify f {n} r = cases (restrict f n ≡NFRestr? r)
    where
        cases 
            : (Dec (restrict f n ≡ r)) 
            → Choices r 
            → Bool
        cases (yes refl) c = does (f-choice ≡? c)
            where
                f-choice : Choices (restrict f n)
                f-choice = getChoiceFromExence (restrict+ f) n
        -- If r is already different from f, then reject all choices.
        cases (no _) c = false 

MFF-filterify : NFFun → MFF
MFF-filterify = Filter→MFF ∘ filterify

filterify-self-sats
    : (f' : NFFun)
    → NFFun-sats (filterify f') f'
filterify-self-sats f' = ?

-- A Singleton Filter is a filter that is satisfied by exactly one relation.
IsSingleton : Filter → Set
IsSingleton F = 
    Σ[ f ∈ NFFun ] (NFFun-sats F f) × ((g : NFFun) → NFFun-sats F g → g ≈≈ f)

IsSingleton' : MFF → Set
IsSingleton' = IsSingleton ∘ MFF→Filter

filterify-singleton
    : (f' : NFFun)
    → IsSingleton (filterify f')
filterify-singleton = ?

filterify-deadendfree
    : (f' : NFFun)
    → DeadEndFree (filterify f')
filterify-deadendfree = ?

-- The only NFFun that satisfies `filterify f` is `f` itself (up to function
-- extensionality).
-- This is the specification of `filterify`, so this lemma proves
-- the correctness of `filterify`.
filterify-unique-sat
    : (f' g' : NFFun)
    → NFFun-sats (filterify f') g'
    → g' ≈≈ f'
filterify-unique-sat = {! #TODO: Should be corollary of the above two lemmas !}

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
-- where F_R = Filter→MFF (filterify R).
-- (That that is a singleton does require a lemma).

-- #QUESTION : define this in terms of EqRel or NFFuns?
-- Currently using EqRel since the definition is quite extensional,
-- from an NFFun one cannot immediately tell which elements are related.
-- One can by converting the NFFun to an EqRel or by (1) converting it to an
-- Exence and 
-- (2) using the AreRelated defined in Eser.Filters.NormalityInNFRestr.
Rel-sats' : MFF → EqRel → Set
Rel-sats' = Rel-sats ∘ MFF→Filter

_relates_to_ : EqRel → ℕ → ℕ → Set
(R , _) relates x to y = T (R x y)

relates-to-refl : (R : EqRel) → Reflexive (R relates_to_)
relates-to-refl = ?

relates-to-sym : (R : EqRel) → Symmetric (R relates_to_)
relates-to-sym = ?

relates-to-trans : (R : EqRel) → Transitive (R relates_to_)
relates-to-trans = ?

-- R ⊆ S if S relates all pairs (x, y) that R relates.
_⊆_ : EqRel → EqRel → Set
R ⊆ S = ((x y : ℕ) → R relates x to y → S relates x to y)

⊆-refl : (R : EqRel) → R ⊆ R
⊆-refl R x y xRy = xRy

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
--------------------------------------------------------------------------------
-- Uniqueness of P-closure
--------------------------------------------------------------------------------
-- The definition of a closure of a relation already implies it is
-- unique, at least up to function extensionality.
 
-- Extensional equality between relations: 
-- homotopy between the underlying ℕ → ℕ → Bool functions.

_≣_ : EqRel → EqRel → Set
(R , _) ≣ (S , _) = R ≈ S

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
    where
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
    → F Allows c In r 
    → F Allows c' In r 
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
    → F Allows c In r
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

AlwaysFires : MFF → Set
AlwaysFires F = {n : ℕ} → (r : NFRestr n) → IsFire (F r)

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
    where
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
-- Composing equality filters
--------------------------------------------------------------------------------
-- Theorems showing the properties of _⋗_ compositions of EqFilters.

-- Same-extender-up-to-function-extensionalty relation.
-- (Output relations are homotopic).
_=ext_ : Extender → Extender → Set
G =ext F = (R : EqRel) → proj₁ (proj₁ $ G R) ≈ proj₁ (proj₁ $ F R)


todo : Set
todo = {! move <Path to own file !}

-- 𝐓𝐡𝐞𝐨𝐫𝐞𝐦
-- Let S be the E-closure of R.
-- Then x S y iff there exists a path 
--      x = z_1 < z_2 < ... < z_k = y
-- where for each i either 
--      z_i R z_{1+i} 
-- or 
--      Eq E z_i z_{i + 1}.
eqfilter-closure-characterisation
    : (E : EqFilter)
    → (R : EqRel)
    → (x y : ℕ)
    → ((proj₁ $ (∗ E) R) relates x to y) ↔ (TriPath (R relates_to_) (Eq E) x y)
eqfilter-closure-characterisation = ?
 
-- 𝐓𝐡𝐞𝐨𝐫𝐞𝐦
-- When closing by multiple equation filters, the order does not matter.
eqfilter-closure-commutes
    : (E E' : EqFilter)
    → (∗ E ⋗ ∗ E') =ext (∗ E' ⋗ ∗ E)
eqfilter-closure-commutes E E' = {! See sheet exco 6. Depends on prev lemma. !}

id-Extender : Extender
id-Extender R = (R , ⊆-refl R)

eq-list-closure : List EqFilter → Extender
eq-list-closure [] = id-Extender
eq-list-closure (E ∷ Es) = ∗ E ⋗ (eq-list-closure Es)

Eq' : List EqFilter → ℕ → ℕ →  Set
Eq' L x y = Any (λ E → Eq E x y) L

eqfilter-closure-compos-subrelat
    : {L : List EqFilter}
    → {R : EqRel}
    → {x y : ℕ}
    → Eq' L x y
    → ((proj₁ $ (eq-list-closure L) R) relates x to y) 
eqfilter-closure-compos-subrelat {[]} {R} {x} {y} ()
eqfilter-closure-compos-subrelat {E ∷ Es} {R} {x} {y} (here xEy) =
    eqfilter-closure-subrelat {E} {S'} {x} {y} xEy
    where
        S' : EqRel
        S' = proj₁ $ (eq-list-closure Es) R
eqfilter-closure-compos-subrelat {E ∷ Es} {R} {x} {y} (there any) = xSy
    where
        S : EqRel
        S =  proj₁ $ (eq-list-closure (E ∷ Es)) R
        -- ^ That equals `proj₁ $ (∗ E) S'`
        S' : EqRel
        S' = proj₁ $ (eq-list-closure Es) R
        S'⊆S : S' ⊆ S
        S'⊆S = proj₂ $ (∗ E) S'
        xS'y : S' relates x to y
        xS'y = eqfilter-closure-compos-subrelat {Es} {R} {x} {y} any
        xSy : S relates x to y
        xSy = S'⊆S x y xS'y


Eq'-⊎
    : {Es : List EqFilter}
    → {E : EqFilter}
    → {x y : ℕ}
    → (Eq' Es ⊎⊎ Eq E) x y
    → Eq' (E ∷ Es) x y
Eq'-⊎ {Es} {E} {x} {y} = ↔-to $ Any-⊎-right (λ E → Eq E x y) E Es
    where
        open import Eser.Data.List.Relation.Unary.Any.Properties
            using (Any-⊎-right)

-- 𝐓𝐡𝐞𝐨𝐫𝐞𝐦
-- Generalisation of `eqfilter-closure-characterisation` to compositions
-- of equations. 
-- Shows that the output of the L-closure is just R extended with
-- the equations in L and closed under transitivity.
eqfilter-closure-composition
    : (L : List EqFilter)
    → (R : EqRel)
    → (x y : ℕ)
    → ((proj₁ $ (eq-list-closure L) R) relates x to y) 
      ↔ 
      (TriPath (R relates_to_) (Eq' L) x y)
-- Proof strategy: induction on L. 
-- In the L ≗ [] case both sides are just xRy.
-- In the L ≗ (E ∷ Es) case both directions needs to be shown separately.
-- Let S ≔ proj₁ $ (eq-list-closure L) R.
-- 1. Assume xSy. eqfilter-closure-characterisation gives a path
--   containing S' and E as steps, where S' ≔ proj₁ $ (eq-list-closure Es) R.
--   The IH allows to rewrite the S'-steps into sub-paths over R and Es.
--   Then apply a 'flatten' lemma to make this into one path.
-- 2. For the other direction, a path is given, and proceed by induction
--   on the path, inductively proving that every step xTy implies xSy,
--   and then conclude by transitivity of S.
eqfilter-closure-composition [] R x y = {! ans !}
    where
        path→R : <Path (R relates_to_) (Eq' []) x y → R relates x to y
        path→R = path-uninhabited-right (λ x y → ¬Any[]) (relates-to-trans R)

        R→path : R relates x to y → <Path (R relates_to_) (Eq' []) x y
        R→path xRy = laststep {! x<y !} $ inj₁ xRy

        -- The goal simplifies to this:
        ans : (R relates x to y) ↔ <Path (R relates_to_) (Eq' []) x y
        ans = (R→path , path→R)
eqfilter-closure-composition (E ∷ Es) R x y = (to x y , from x y)
    where
        S : EqRel
        S = proj₁ $ (eq-list-closure (E ∷ Es)) R

        -- S' is the same as S but not yet closed under E.
        -- I.e., S is the E-closure of S'.
        S' : EqRel
        S' = proj₁ $ (eq-list-closure Es) R

        check : S ≡ proj₁ ((∗ E) S')
        check = refl


        to-< 
            : {x y : ℕ}
            → x < y 
            → S relates x to y 
            → <Path (R relates_to_) (Eq' (E ∷ Es)) x y
        to-< {x} {y} x<y xSy = flatpath'
            where
                lastclosure 
                    : S relates x to y 
                    → TriPath (S' relates_to_) (Eq E) x y
                lastclosure = 
                    ↔-to 
                        {S relates x to y} 
                        {TriPath (S' relates_to_) (Eq E) x y}
                        $ eqfilter-closure-characterisation E S' x y
                nestedpath : <Path (S' relates_to_) (Eq E) x y
                nestedpath = tripath-elim-< (lastclosure xSy) x<y

                IH  : {x y : ℕ}
                    → S' relates x to y 
                    → TriPath (R relates_to_) (Eq' Es) x y 
                IH {x} {y} = ↔-to (eqfilter-closure-composition Es R x y)

                nestedpath' : <Path (TriPath (R relates_to_) (Eq' Es)) 
                                    (Eq E) x y
                nestedpath' = path-map-left {S' relates_to_} {Eq E} 
                                {TriPath (R relates_to_) (Eq' Es)} 
                                IH {x} {y} nestedpath
                -- The TriPath steps must all be <Path steps in the same
                -- direction.
                nestedpath'' : <Path (<Path (R relates_to_) (Eq' Es)) (Eq E) x y
                nestedpath'' = nested-tripath-left nestedpath'

                flatpath : <Path (R relates_to_) (Eq' Es ⊎⊎ Eq E) x y
                flatpath = path-flatten-left nestedpath''

                flatpath' : <Path (R relates_to_) (Eq' (E ∷ Es)) x y
                flatpath' = path-map-right Eq'-⊎ flatpath
        to 
            : (x y : ℕ)
            → S relates x to y 
            → TriPath (R relates_to_) (Eq' (E ∷ Es)) x y
        to x y = cases (<-cmp x y)
            where
                cases 
                    : Tri (x < y) (x ≡ y) (x > y)
                    → S relates x to y 
                    → TriPath (R relates_to_) (Eq' (E ∷ Es)) x y
                cases (tri< x<y _ _) xSy = samedir x<y $ to-< {x} {y} x<y xSy
                cases (tri≈ _ x≡y _) = λ _ → emptypath x≡y
                cases (tri> _ _ y<x) xSy = oppdir y<x 
                    $ to-< {y} {x} y<x (relates-to-sym S {x} {y} xSy )

        R⊆S : R ⊆ S
        R⊆S = ?

        L→S : {x y : ℕ} → (Eq' (E ∷ Es) x y) → S relates x to y
        L→S = ?

        from-samedir 
            : {x y : ℕ}
            → <Path (R relates_to_) (Eq' (E ∷ Es)) x y 
            → S relates x to y
        from-samedir (laststep {x} {y} x<y (inj₁ xRy)) = R⊆S x y xRy
        from-samedir (laststep {x} {y} x<y (inj₂ xLy)) = L→S xLy
        from-samedir (addstep {x} {z} {y} x<z z<y (inj₁ xRz) p) = 
            relates-to-trans S {x} {z} {y} (R⊆S x z xRz) (from-samedir p)
        from-samedir (addstep {x} {z} {y} x<z z<y (inj₂ xLz) p) =
            relates-to-trans S {x} {z} {y} (L→S xLz) (from-samedir p)

        from 
            : (x y : ℕ) 
            → TriPath (R relates_to_) (Eq' (E ∷ Es)) x y 
            → S relates x to y
        from x y (samedir {x} {y} x<y p) = from-samedir p
        from x y (emptypath refl) = relates-to-refl S {x}
        from x y (oppdir {x} {y} y<x p) = 
            relates-to-sym S {y} {x} (from-samedir {y} {x} p)
    
-- 𝐂𝐨𝐫𝐨𝐥𝐥𝐚𝐫𝐲
-- Every equation in L : List EqFilter holds in the L-closure of R.
open import Data.List.Membership.Propositional
open import Data.List.Relation.Unary.All as All
-- #TODO L choose which (or both) of the two below to prove.
-- Both should be easy given the previous theorem (or the other).
-- When removing one statement, also remove the associated import.
eqfilter-closure-composition-anyeqs
    : (L : List EqFilter)
    → (R : EqRel)
    → {E : EqFilter}
    → E ∈ L
    → (x y : ℕ)
    → Eq E x y
    → (proj₁ $ (eq-list-closure L R)) relates x to y
eqfilter-closure-composition-anyeqs = ?
eqfilter-closure-composition-alleqs
    : (L : List EqFilter)
    → (R : EqRel)
    → (x y : ℕ)
    → All (λ E → Eq E x y → (proj₁ $ (eq-list-closure L R)) relates x to y) L
eqfilter-closure-composition-alleqs = ?

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

