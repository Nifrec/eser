# Signatures and beyond
31 October 2025

## External arguments from finite sets
It is *not* a generalisation of signatures to allow constructors to take,
aside from a finite number of recursive arguments,
also a finite number of arguments from external finite sets.
If `c` takes arguments `a_1, a_2, ..., a_n` from sets `A_1, A_2, ..., A_n`
then one obtains the same terms by using the signature without external
arguments but a constructor `c_{a_1, a_2, ..., a_n}` for every
`(a_1, a_2, ..., a_n) ∈ A_1 × A_2 × ... A_n`.

## External arguments from countable sets
* There is nothing to gain by adding *multiple* (but still finitely many)
    arguments from countable sets.
    This is because ℕⁿ≅ℕ. I.e., Cartesian products of countable sets are still
    countable, 
    so one can input one `n`-tuple as argument instead of `n` arguments.
    So, there is no loss in generality by allowing at most one external
    countable argument.
* If constructor `c` takes one countable external argument, w.l.o.g. from ℕ,
    we still can define a sensible total linear chain order, for example as
    follows: during cycle `h`, we include all terms with top-level constructor
    `c` that take as arguments:
    - one recursive argument from cycle `h-1`, other recursive arguments
        from any previous cycle, and as external number any `n ≤ h`.
    - all recursive arguments from cycles at most `h-2`, 
        and external number `n ≤ h+1`.
    Then all possible terms constructed via `c` will still be enumerated exactly
    once.
* This shows that signatures-with-constructors-with-countable-external-arguments
    (say signatures+) are still Signoids. 
    And hence signature+s together with decidable equalities
    between terms are representable as StreamGrids.
* The countable arguments can come from other signature+s as well, 
    because I just showed they are countable.
* In light of the above, I conjecture:
    **Conjecture: all inductive types whose constructor's 
        arguments are decidable inductive types are Signoids.**
    If we add decidable equalities between the terms of such types,
    then we more or less would get this:
    **All decidable inductive types depending only on decidable inductive
        types are representable as StreamGrids**.
    Now that'd be a very cool result.
    Also a bit confusing...
    - All such types are some sort of grids?
    - Better name: StreamTypes i.o. StreamGrids?
    - Signoids seems very general things?
    - Would this be a useful characterisation of all decidable purely inductive
      types?
