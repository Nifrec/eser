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

## A new solution: partial terms
The problem is that the vector-of-arguments is too much of a black box.
So let's do away with it, and give arguments one-by-one.
Then every argument appears explicitly in the inductive structure of a term.
```agda
-- PartialTerms n are the partially constructed terms
-- that still need n inductive arguments.
-- PartialTerms 0 are exactly the closed terms of the term algebra.
data PartialTerms (S : TerseSignature) : ℕ →  Set where
    mk-pure-nullary : Fin (pure-nullary S) → PartialTerms S 0
    mk-ℕ-nullary : Fin (ℕ-nullary S) → ℕ → PartialTerms S 0
    argless-pure-multiary 
        : (c : indices (pure-multiary S)) 
        → PartialTerms S (ℕ.suc (Data.List.lookup (pure-multiary S) c))
    argless-ℕ-multiary 
        : (c : indices (pure-multiary S)) 
        → ℕ
        → PartialTerms S (ℕ.suc (Data.List.lookup (pure-multiary S) c))
    giveArg
        : {n : ℕ}
        → PartialTerms S (ℕ.suc n) --^ Term still needing at least 1 more arg.
        → PartialTerms S 0         --^ Next argument to give: a closed term.
        → PartialTerms S n
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
