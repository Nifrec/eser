# The subterm induction problem
3 March 2026

## Problem
`decomposeTerm : TerseFreeTerms → TeleTerms` de-constructs the choices
that went into the construction of a term.
But a term takes a *vector* of arguments `L`, 
and we need to de-construct them to `TeleTerms` as well. 
But now, anything similar to `map decomposeTerm L` will make the termination
checker very dissatisfied!

## Failed solution
Define the subterm relation, prove that it is Well-Founded, and define
`decomposeTerm` via Well-Founded induction.
```agda
-- Is-argument relation
_«_ : Rel (TerseFreeTerms S) 0ℓ
a « mk-pure-nullary _ = ⊥           --^ Nullary terms have no argument.
a « mk-ℕ-nullary _ _ = ⊥            --^ Nullary terms have no argument.
a « mk-pure-multiary c L = a ∈ L    --^ L is the list of arguments.
a « mk-ℕ-multiary c L _ = a ∈ L     --^ L is the list of arguments.

-- The 'subterm' relation is the transitive closure of _«_.
_«*_ : Rel (TerseFreeTerms S) 0ℓ
_«*_ = TransClosure _«_ 
```
But how to prove either of these is Well-Founded?
Well-Founded recursion on (ℕ, <) on the height of a term?
```agda
height : TerseFreeTerms S → ℕ
height (mk-pure-nullary _)    = 0
height (mk-ℕ-nullary _ _)     = 0
height (mk-pure-multiary c L) = ℕ.suc (max 0 (map height (toList L)))
height (mk-ℕ-multiary c L _)  = ℕ.suc (max 0 (map height (toList L)))
```
Looks good to me, but not to the termination checker, since Agda doesn't see
that `map height (toList L)` only applies `height` to subterms.
This does work:
```agda
height : TerseFreeTerms S → ℕ
height (mk-pure-nullary _)    = 0
height (mk-ℕ-nullary _ _)     = 0
height (mk-pure-multiary c (x ∷ L)) = ℕ.suc (height x)
height (mk-ℕ-multiary c (x ∷ L) _) = ℕ.suc (height x)
```
since `x` is an explicit subterm, but obviously computes a bogus number.

## A new solution: open terms
The problem is that the vector-of-arguments is too much of a black box.
So let's do away with it, and give arguments one-by-one.
Then every argument appears explicitly in the inductive structure of a term.
```agda
-- OpenTerms n are the partially constructed terms
-- that still need n inductive arguments.
-- OpenTerms 0 are exactly the closed terms of the term algebra.
data OpenTerms (S : TerseSignature) : ℕ →  Set where
    mk-pure-nullary : Fin (pure-nullary S) → OpenTerms S 0
    mk-ℕ-nullary : Fin (ℕ-nullary S) → ℕ → OpenTerms S 0
    argless-pure-multiary 
        : (c : indices (pure-multiary S)) 
        → OpenTerms S (ℕ.suc (Data.List.lookup (pure-multiary S) c))
    argless-ℕ-multiary 
        : (c : indices (pure-multiary S)) 
        → ℕ
        → OpenTerms S (ℕ.suc (Data.List.lookup (pure-multiary S) c))
    giveArg
        : {n : ℕ}
        → OpenTerms S (ℕ.suc n) --^ Term still needing at least 1 more arg.
        → OpenTerms S 0         --^ Next argument to give: a closed term.
        → OpenTerms S n
```

(Also recall that 
```agda
-- Very terse representation of signatures.
-- Constructors either have arity 0 or suc a
-- (for inductive arguments of their own type;
-- for each multiary constructor with arity `suc a`,
-- the value `a` should be stored in the List ℕ).
-- Constructors either take one external argument from ℕ,
-- or no external arguments.
record TerseSignature : Set where
   field 
        pure-nullary : ℕ
        ℕ-nullary    : ℕ
        pure-multiary : List ℕ
        ℕ-multiary : List ℕ
```
)

## Follow-up problems
4 March 2026

Now the above gave a very elegant way of defining _«_:
```agda
AllOpenTerms : (S : TerseSignature) → Set
AllOpenTerms S = Σ[ n ∈ ℕ ](OpenTerms S n)

ClosedTerms : (S : TerseSignature) → Set
ClosedTerms S = OpenTerms S 0

module _ {S : TerseSignature} where
    -- Is-argument-of-relation: 
    -- `a « t` iff t is build as a contructor with (among others) argument a.
    -- a is an arument of (giveArg t a₁) if it is the last 
    -- argument (a₁) or an earlier argument, i.e., an arg of t.
    -- This relation also concerns non-closed-terms, it was easier to define it
    -- this way.
    _«_ : Rel (AllOpenTerms S) 0ℓ
    a « (0 , mk-pure-nullary _)           = ⊥
    a « (0 , mk-ℕ-nullary _ _)            = ⊥
    a « (suc n , argless-pure-multiary _) = ⊥
    a « (suc n , argless-ℕ-multiary _ _)  = ⊥
    a « (n , giveArg t a₁)                = (a ≡ (0 , a₁)) ⊎ (a « (ℕ.suc n , t))
```
Unfortunately, `(ℕ.suc n , t)` is not the same as `t` and the termination
checker rejected it...

### Better solution
Use a relation that is heterogeneous in the indices of the underlying type:
```agda
_«_ : {n m : ℕ} → (OpenTerms S n) → (OpenTerms S m) → Set
a « mk-pure-nullary _           = ⊥
a « mk-ℕ-nullary _ _            = ⊥
a « argless-pure-multiary _     = ⊥
a « argless-ℕ-multiary _ _      = ⊥
_«_ {0} {m} a (giveArg t a₁)    = (a ≡ a₁) ⊎ (a « t)
_«_ {suc n} {m} a _             = _ 
```
Now we cannot simply take the `TransClosure`, since the stdlib only defines
it on homogeneous relations.
But we can mimick the definition thereof easily:
```agda
module IndexHeterogeneousTransClosure 
    {I : Set}
    {A : {I} → Set}
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
    data ITransClosure (_∼_ : {i j : I} → A {i} → A {j} → Set) 
                      : {i j : I} → A {i} → A {j} → Set where
        direct 
            : {i j : I} 
            → (a : A {i}) 
            → (b : A {j}) 
            → (a ∼ b) 
            → ITransClosure _∼_ a b
        composed --^ a∼b and b∼⁺c then a∼⁺c.
            : {i j k : I} 
            → (a : A {i}) 
            → (b : A {j}) 
            → (c : A {k})
            → a ∼ b
            → ITransClosure _∼_ b c
            → ITransClosure _∼_ a c
open IndexHeterogeneousTransClosure
```
And now we can define the is-subterm-of-relation:
```agda
_«*_ : {n m : ℕ} → (OpenTerms S n) → (OpenTerms S m) → Set
_«*_ {n} {m} = ITransClosure _«_ {n} {m}
```
