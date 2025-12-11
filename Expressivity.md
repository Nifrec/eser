# Expressivity of StreamGrids
*What kind of relations can we describe this way?*

* It is designed for congruence equivalences over term algebras for signatures.
  Consequently, it is mostly suited for equivalence relations.
  Although, one can of course extract an asymmetric relation
  by taking the intersection between the constructed equivalence
  and the enumeration relation `«` (which has `x « y` iff the index of `x` in
  the enumeration is smaller than that of `y`).

## Example: inexpressive relation
Let `a « b « c` be an enumeration of a 3-element type `A`.
And let `R ⊆ A×A` be a relation such that `aRc` and `bRc` but not `aRb`.
After two decisions, the state of the StreamGrid would be
```
[ [a] , [b] ]
```
and we would need to decide in which class to put `c`: either in `[a]`, in `[b]`
or in a new class. But we need `aRcRb`, which is not possible since we cannot
make the classes `[a]` and `[b]` equal anymore.

The symmetric-transitive closure of `R` can actually still be expressed as a
StreamGrid, if we change the order of the enumeration to `c « a « b`
(or to `c « b « a`).
Then the evolution of the states of the StreamGrid would be:
```
0. [[c]]
1. [[c, a]]
2. [[c, a, b]]
```

## Something we always can do
Let $A = \{A_0, A_1, A_2, \dots\}$ be an enumerable type
and let $R \in A \times A$ be an arbitrary relation,
and $R^*$ the reflexive-transitive-symmetric closure of R.
Let $R_i$ is the reflexive-transitive-symmetric closure of
the restriction of $R$ to $\{A_0, A_1, \dots, A_i\}$.
Then we can encode $R^*$ as a StreamGrid if $R$ has the following property:

$A_i R^* A_j$ iff $A_i R_{\max(i, j)} A_j$.

For proof on paper: see 11 Dec 2025 metalemma sheet.
