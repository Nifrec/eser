# StreamGrids
TODO: explain what this is all about...

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
    

## TODOs
* Write better README
* Rename 'algebra' to 'signature'

### To test:
* `Enumeration`
* `getEnumerator`
* `getIndex`

### To check if exists in library:
* Definition of `monotone` (used in def `Signoid`).

## Ideas for extensions and explanations

### Applications
* Propositional truncation without HIITs.
* Integers & rational numbers.
* Other HIITs / more complicated inductive types / advanced grids.

### Concrete ideas
* Prove all enumerable inductive types embed into StreamGrids.
    - Is there also a backward map? What is the largest class of types that are
      all StreamGrids?
* Prove that `SGToType` is an hSet.
* Coloured grids.
    * Next step: local rules & CA.
* Enforcing additional constraints such as associativity.
* Defining morphisms between StreamGrids:
    - Weak morphisms: preserve equalities between elements.
    - Strong morphisms: preserve *also* the enumeration, _<_ and _⊂_.
    - For signatures, might also consider morphisms that send
      constructors-to-constructors-with-same-arity.

### Abstract ideas
* Modal logic for arbitrary signatures?
* Regular expressions for arbitrary signatures?
* Dependent coalgebras?

### To explain
* Why signatures with constructors with external args from external
    finite sets are *not* a generalisation: one can add more constructors
    instead, one for each pair of external arguments.

# Alphabet representation issues
**This part of the README is not very relevant anymore!**

## Philosophically: what is an alphabet?
It is a set `A` with the following properties:
1. It is not empty.
2. We can form lists (strings) over it.
3. It is finite.
4. It is linearly ordered 
 (hence strings over A are lexicographically ordered).

## Attempt 1
Alternative definition of a list.
Ensures at type level that the alphabet is not empty and
gives it automatically a linear order.
**Problem:** overcomplicated, the `≢` is really inconvenient in constructive
mathematics.
```agda
data Alphabet (X : Set) : Set 
data notInAlphabet {X : Set} : Alphabet X → X → Set

data Alphabet X where
    least   : X → Alphabet X
    add     : (A : Alphabet X) → (x : X) → notInAlphabet A x → Alphabet X

data notInAlphabet {X} where
    singleton : {x x' : X} → (x ≢ x') → notInAlphabet (least x) x'
    addNew    : (x x' : X) 
              → (x ≢ x') 
              → (A : Alphabet X) 
              → (px : notInAlphabet A x) 
              → (px' : notInAlphabet A x') 
              → (notInAlphabet (add A x px) x')
```

## Attempt 2
A set `A` is finite if, in order to define a function out of `A`,
we only need to choose `n` different output values for some natural number `n`.
**Problem:** universe issues, `∀ P` iterates over all types in the universe.
```agda
Alphabet : Set → Set
data NonEmptySet (A : Set) : Set
FinIterable : Set → Set

Alphabet A = (NonEmptySet A) × (FinIterable A)

data NonEmptySet A where
    witness : A → NonEmptySet A

FinIterable A = Σ[ n ∈ ℕ ] ∀ P → ((Fin n → P) → (A → P))
```

## Attempt 3
Simple and stupid:
```agda
Alphabet : ℕ → Set
Alphabet n = Fin (suc n)

NamedAlphabet : ℕ → Set
NamedAlphabet n = (Alphabet n) × (Fin (suc n) → String)
```

# Lessons learned

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
