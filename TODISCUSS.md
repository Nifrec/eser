# To discuss or tell

## Enumerations
    Annoyed by needing a case distinction between finite and countable types.
    Current idea: give a parameter `numEl ∈ {ℕ , ∞}` that gives the size
    of the set, and only specify the behaviour of the enumerator `ℕ → A`
    on inputs smaller than this size.

## Bialgebras or stronger types?
    I assume a signoid has been given and that `Q` is the type of partially
    explored but otherwise consistent grids (= partially defined equivalences)
    over this sigmoid.
    1. I could model StreamGrids as bialgebras
        ```
        Q --> [Q] --> Q
           σ       δ
        ```
        Here σ is part of the definition of the StreamGrids framework; it is
        hardcoded, it are the allowed successors of a partially explored grid.
        But δ is what the user provides: the decider of equivalences,
        making locally a choice what to do with the next element to decide.
        (the list functor could also be the powerset or ordered lists).
        - The type `[Q]` is bigger than needed, not all elements will be
          reached.
        - The output of `δ` must be in the input list, of course!
    2. I could also type δ stronger, as
        ```agda
        δ : (q : Q) «σ(q)» 
        ```
        where `«...»` lifts a list (or set, or so) to a type whose terms
        are the element of the list.
        I think this approach guarantees that function extensionally
        holds for the δs.

## Permutations
The Agda library apparently defines multiple definitions of
IsAPermulation-relations for lists.
This one is particularly interesting
(from `Data.List.Relation.Binary.Permutation.Propositional`):
```agda
data _↭_ : Rel (List A) a where
  refl  : xs ↭ xs
  prep  : ∀ x → xs ↭ ys → x ∷ xs ↭ x ∷ ys
  swap  : ∀ x y → xs ↭ ys → x ∷ y ∷ xs ↭ y ∷ x ∷ ys
  trans : xs ↭ ys → ys ↭ zs → xs ↭ zs
```
It is *exactly* the definition that took me so much effort to find!

## Abel 2007's paper
* *Monotone operator*?
* Difference recursion and corecursion? Number of arguments?
* *Unguarded* sets of terms can be smaller than guarded ones?
    But how can make adding more terms something 'safer'?
    Or is 'guarded' just a misleading name?
