## Normalising non-terminating λ-expressions

**Edit:**
Bad idea that won't work.
`λ f . f (f (f (f f) ) ) (λ x . c)` where `c` is a constant
expands after 1 β-reduction, but eventually reaches the fixpoint `c`.
So picking the shortest out of 1-β-step and 1-anti-β-step is too greedy.
There would be different classes for computationally equivalent terms!

30 April 2026

*A wild idea.*

If it works then it won't make it for the 15 June deadline anyway,
but even if it remains a thought experiment then I still find it very
interesting.

**Observations:**
* All terms of untyped λ-calculus are terms over an enumerable inductive type.
* β-reduction gives one way to relate terms.
    But β-reducing `(λ f . f f)(λ f . f f)` results in itself.
    Even worse, a single β-step of `(λ g . g (g g))(λ f . f f)` makes the thing
    longer. So «applying β-reductions until a fixpoint is reached» is not a
    valid normalisation option.
* But any term is a finite string with finitely many strict subterms.
    So there are only finitely many possible abstractions
    ('anti-substitutions').
    E.g. `(f x) (f x) |-> (λ g . g g)(f x)`.
* Given a term `t`, we can try all possible 'anti-substitutions' 
    and β-reductions, and call the shortest result the 
    'one-step-χ-reduction' (this needs a better name) of `t`
    (if `t` is shorter than any of those results, then use `t` itself as its
    'one-step-χ-reduction').
* Since a χ-reduction either is the identity (so the input is a fixpoint on
  χ-reductions) or results in a smaller term, we can recursively define
  a normal-form function 
  ```agda
  f : L → L
  f t = if χ(t) = t then x else f (χ t)
  ```
  (where `L` are all terms) that satisfies
  ```agda
  f (f t) = f t
  f t ≤ t
  ```
**Conclusion:**
We can use `f` with the framework I have build in this project,
to define a quotient `L / f` whose classes are equivalent terms.
- The quotient map is now some sort of function evaluation.
    But it is compatible with non-halting expressions!
- Normal forms are the shortest expressions of a class. 
    They may not be fixpoints of β-reduction (!), 
    but this is necessary, since for non-halting computations 
    such fixpoints don't exist.
- For halting computations, I *suspect* the output is usually a fixpoint of
    β-reduction. (Maybe even provably so?)

