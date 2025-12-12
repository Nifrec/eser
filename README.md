# StreamGrids
TODO: explain what this is all about...
And how the readme is organised.

Other files of interest:
* [./Signoids.md] : discussion on the design of Signoids.
* [./TODISCUSS.md] : things to discuss with superviors.
* [./Expressivity.md] : discussion what kinds of relations StreamGrids can
  encode.

## What is where
* `StreamGrids/Fold`    
    Function to fold finite sets.
* `StreamGrids/Algebra` 
    Representation of finite-arity algebras/signatures.
* `StreamGrids/Practise`
    No library functions; just experiments with Agda, 
    to try out what is possible.
* `StreamGrids/Enumeration`
    Predicate telling that a set is enumerable.
* `StreamGrids/Chain`
    Definition of total linear order relations.
* `StreamGrids/Examples`
    Example instantiations of abstract definitions,
    also functions as test cases.
    `StreamGrids.Examples.Foo` contains the examples for
    module `StreamGrids.Foo`.
* `StreamGrids/Practise`
    Informal personal practise to get better acquainted with Agda.

## Naming conventions

### Acronyms & abbreviations
* 'SG' means 'StreamGrid'.
* 'SGS' means 'StreamGrid state'.
* 'NF' means 'normal form'. 
    For StreamGrid elements, it is the lexicographically least element
    in an equivalence class under the encoded congruence.
* 'card' means 'cardinality'.
* `L' ≼ L` means that `L'` is a 'suffix' of `L`',
    i.e., `L'` are the oldest `n` element of `L` for some `n ≤ length L`.

### Nested lists
In a list of lists `LS = [ L1 , L2 , L3 , ...]` 
where each Li : List A and where LS : List (List A),
I will call:
* Ls the **toplist**
* Li a **lowlist**
**Warning:** old comments (pre-22 Nov 2025)
might still confuse 'sublist' and 'lowlist'.
'Sublist' always means 'lowlist'.
    

## TODOs
* Everywhere I call `_⊂_` a *subterm* relation, while it is a 
    *is-a-direct-argument* relation!
* Why do we keep `_«_` in Signoids?
    It is just the `_<_` on indices in the enumeration anyway!
    More precisely, `_«_` is the relation
    `x, y -> cardTo< (getIdx x) (getIdx y)`.
* Document the types in `ChoiceLog.Core.agda`.
* Finish stuff in `Signoid.agda`.
* Remove/archive deprecated source files.
* Update What-is-Where.
* Write better README.
* Rename 'algebra' to 'signature'.
* Update `Experimental` status in file headers.
* Handle `#TODO`s in source files.
* Remove superfluous imports.
* Cleanup/update old stuff readme
    - Nested lists
    - Latest handwritten version


### To check if exists in library:
* Definition of `monotone` (used in def `Signoid`).

## Where to find handwritten stuff

### 8 Dec version of Signoids
#### Updated defs 
Of `Signoid`, `nf()`, `LegalChoices`, see *connf (9)*.
#### Lemma: confluence normalisation for term-algebras
The lemma proving *independence of the specific coercion in the LegalChoices
constructor for the output of `nf()` in the case of term-algebras*,
is in on sheet *connf (8)*, the related definitions on the next page.

### 11 Dec 2025 proof of encodability certain relations
See 11 Dec 2025 metalemma sheet and also [./Expressivity.md].

## Ideas for extensions and explanations

### Applications
* Propositional truncation without HIITs.
* Integers & rational numbers.
* Other HIITs / more complicated inductive types / advanced grids.
* Prove that `SGToType` is an hSet.

### Concrete ideas
* Prove all enumerable inductive types embed into StreamGrids.
    - Is there also a backward map? 
    - What is the largest class of types that are all StreamGrids?
    - Maybe the initial algebras of a certain class of functors?
* Coloured grids.
    * Next step: local rules & CA.
* Enforcing additional constraints such as associativity.
* **Defining morphisms** between StreamGrids:
    - Weak morphisms: preserve equalities between elements.
    - Strong morphisms: preserve *also* the enumeration, _<_ and _⊂_.
    - For signatures, might also consider morphisms that send
      constructors-to-constructors-with-same-arity.
* **Multiple roots**: why one enumeration with one 0-element?
    We can have multiple roots. This can be done in different ways:
    - Restrict to strings, and have multiple "empty strings".
        *Eh this is nothing new! It is just a term algebra with multiple
        nullary constructors...*
    - Different enumerations of `A`; this idea is probably best combined with
      *Directed StreamGrids* (see *Abstract ideas* below).

### Ideas for examples
* PropTrunc:
    * List membership.
    * List permutation equivalence.

### Abstract ideas
* **Directed StreamGrids**: see equalities as outgoing.
    If `q = [..., [x_1, x_2, x_3, ...], ...]` is a state
    then we can interpret this also as directed equalities `x_1 -> x_2 -> x_3`
    instead of `x_1 = x_2 = x_3`. 
    Is this somehow related to Andrea's work?
* Composability of filtering functions
    relat X 
    <all> -> [all relats X+{A_n}] 
    <σ> -> [all congr equivalences on X+{A_n}]  
        --^ Assuming inp relat is congr.equiv
    <?> -> [all assoc congr equivalences on X+{A_n}]
        --^ Assuming inp relat is assoc
* Modal logic for arbitrary signatures?
* Regular expressions for arbitrary signatures?
* Dependent coalgebras? Computing next allowed states is a coalgebra!
    Q -> List Q
* Kleisli composition of deciders.
* Category of countable sets and (monotone?) functions between them?

### Doubts
* Do we really need to enumerate *all* elements of a type-of-raw-terms?
    Perhaps we want to use only a part of it for our StreamGrid,
    and have our enumeration only enumerate that part (and `_<_` only has the
    right properties for that part).
    **Counterargument**: in such a scenario, if `A` has more raw terms than
    desired, one can probably also define an inductive type `B` with only
    constructors for the desired terms. 
    Maybe not as flexible as allowing partial enumerations, but let's keep
    bijective enumerations `ℕ → A` for now to keep things simpler.

### To explain
* Why states are annotated with a list of normal forms.
    - To avoid circular definitions: do define `LegalChoices`,
    we need to know whether there is a forced coercion, which occurs
    iff some argument of y is not in normal form.
    But we cannot compute the normal forms of the arguments (in the index
    state `q` of `LegalChoices q`), 
    since it would require pattern matching the index state, 
    which also requires pattern matching `LegalChoices`, 
    which in turn depend on something being normal or not...
* Why signatures with constructors with external args from external
    finite sets are *not* a generalisation: one can add more constructors
    instead, one for each pair of external arguments.
* The custom notations (e.g., `listRelat`).
* Why not all monoids fit into the framework: dependency, your input is a
  congruence that you need to extend. It might not be recursively be generated
  by yourself (in practise it is, but you don't know). 
  See LL journal 14 Nov.

# Lessons learned

## 10 & 12 Nov 2025: Coercions instead of any simplification
If a term `c(x)` is a constructor `c` with an argument (a *subterm*) `x`,
and there exists an `x' < x`, then the term `c(x')` also exists
and `c(x') < c(x)`. 
In any Signoid, such a 'coercion' to `c(x')` must exist.
Now if `x ≈ x'` is an equivalence in the partially explored
grid, then we need `c(x) ≈ c(x')` as well.
That's OK, we have `x' < x` so the lexicographical order
ensures also `c(x') < c(x)`, and the state of a grid where `c(x)` is
the next to explore already contains `c(x')`, so the unique successor state can
be the state where `c(x)` is added to the stream of `c(x')`.

But subtleties occur when, for example, `c(x, x')` and `c(x', x)` both exist.
In this case, the following (old definition of Signoid) requirement
allows to coerce `c(x', x)` to the lexicographically bigger `c(x, x')`,
which breaks the algorithm.
```agda
HasSubTermProp
    : {ℓ : Level.Level}
    → {A : Set ℓ} 
    → (_<_ : Rel A ℓ)
    → (_⊂_ : Rel A ℓ)
    → Set ℓ
HasSubTermProp {ℓ} {A} _<_ _⊂_ =
    {x y x' : A} → (x ⊂ y) → (x' < x) → Σ[ y' ∈ A ](
        (y' < y)
        ×
        (x' ⊂ y')
        ×
        ({x'' : A} → (x'' ≢ x) → (x'' ≢ x') → ((x'' ⊂ y) iff (x'' ⊂ y')))
        -- `y'` same subterms as `y` except possibly not `x` and extra `x'`.
        )
```
The solution? There should be a *chosen* coercion that is lexicographically
smaller. 
More precisely, we should coerce *all* instances of the argument,
i.e., coerce both to `c(x', x')`. 
Then the exploration algorithm will force `c(x', x') ≈ c(x, x') ≈ c(x', x)`,
as desired.
Note that `c(x', x')` will be explored first, as desired.
In implementation, this means simply adding `× ¬ (x ⊂ y')` to the type.


## Confusing types and elements
Why does this not work?
```agda
Alphabet : ℕ → Set
Alphabet n = Fin (suc n)

AlgToAlph : (A : Algebra) → Alphabet (Data.Nat.pred (totNumConstr A))
AlgToAlph A = Fin (Data.Nat.suc (Data.Nat.pred (totNumConstr A)))
```
Last line gives a type error while I checked that
both `Alphabet (Data.Nat.pred (totNumConstr A))`
and `Fin (Data.Nat.suc (Data.Nat.pred (totNumConstr A)))`
normalise to `Fin (suc (totNumConstr A ∸ 1))`!

**Solution:** 
A function `f : A → B` needs to output *an element* of `B`. 
Not the type `B`. #facepalm

## 24-27 Nov 2025 use constructors not dependent sums
I started with defining StreamGrid states as lists of lists
that I then Σ-ed with externally proven properties (invariants)
that those lists satisfy:
```agda
-- Partially explored StreamGrid.
-- The equivalences between the first n raw terms have been decided
-- and form an congruence.
-- Note: `Linked _«_` means just 'sorted according to _«_'.
SGState : (n : SIndices) → Set ℓ
SGState n = 
    Σ[ L ∈ List (List A)](
    (IsPrefix L n)
    ×
    (Linked _«_ (firstElem L))
    ×
    (All (λ as → Linked _«_ as) L)
    ×
    (IsCongruence L)
    )
```
This works but it is awfully cumbersome to prove that all variants are retained
when extending a list with a new element.
`Data.List.Membership.Propositional` gives useful tools but it remains
confusing and a lot of work.

**Better: use an inductive type where all invariants are enforced by the
constructors!**
Now I have:
```agda
data SGState where
    empty : SGState StateIdxZero
    choose : {n : StateIndices} 
        → (q : SGState n) 
        → LegalChoices q 
        → SGState (StateIdxSuc n)

next : {n : StateIndices} → IsNotMax n → A
next {n} notMax = Signoid.enum S (cardLower notMax)

data LegalChoices where
    coercion 
        : {n : StateIndices} 
        → (q : SGState n) 
        → ForcedCoercion q 
        → LegalChoices q
    newEquiv
        : {n : StateIndices} 
        → (q : SGState n) 
        → (NoForcedCoercion q )
        → NormalForms q
        --^ Existing element we set the next element equal to.
        → LegalChoices q
    newNF 
        : {n : StateIndices} 
        → (q : SGState n) 
        → (NoForcedCoercion q )
        → LegalChoices q
```

## 27 Nov 2025 why lex order in Signoids?
Why do we keep `_«_` in Signoids?
It is just the `_<_` on indices in the enumeration anyway!
More precisely, `_«_` is the relation
`x, y -> cardTo< (getIdx x) (getIdx y)`.
Right now the def is:
```agda
record Signoid 
    {ℓ : Level.Level} 
    {A : Set ℓ} 
    (_<_ : Rel A ℓ) 
    (_⊂_ : Rel A ℓ) 
    : Set ℓ where
    field
        numEl    : ℕ∞
        enum     : (cardToSet numEl) → A
        mono : Monotonic₁ (cardTo<) (_<_) enum
        surj     : (a : A) → Σ[ n ∈ cardToSet numEl ]( enum n ≡ a)
        chain : Chain _<_
        subrelat : IsSubRelat _<_ _⊂_
        coercion : SubtermCoercion _<_ _⊂_ 
        getIdx : A → cardToSet numEl
        inv : Inverseᵇ _≡_ _≡_ enum getIdx
```
