# The Sublog disaster

16 January 2026
Lulof Pirée

## The mistake
I defined the relation ⋤ wrong.
Currently, `q ⋤ q+` iff `q+` is a stack of choices
extending the stack of choices `q`.
Problem is, this must be a very literal extension: the implementation details
of the choices (such as some proof-irrelevant terms proving a certain option was
an available choice) must be equal in order to prove `q ⋤ q+`.

Analogy: Alice and Bob each plan a route from the south corder of SomeTown
to the northern corner of SomeTown.
They happen to choose the same streets at every turn.
We would like to say they made the *same choices* and walked the *same route*.
But currently my definition of *sameness* is so strict that their series of
choices are only considered to be "the same" if one can prove all context
details of how the choices were made (e.g., patterns of neurons firing in their
brain, using exactly the same map, etc.) are the same.
**These details should not be included in the definition of *same sequence of
choices*!**

### The practical consequence of this bad definition
I spend weeks in hyperfocus crunching on proving all kinds of low-level
details in Agda, especially about Finite sets, e.g., all kinds of equations
relating `inject₁`, `Fin.suc`, `Fin.+`, `cast`, `toℕ`, etc.
Took **a lot** of time and energy, gave complicated proofs, made the story less
comprehensible.

### The "right" way to move forward
1. States should be indexed not only by their height and NFList,
    but by the practical outcomes of the choices.
    I.e., by the list of lists, giving the normal forms of each element
    up to some element `A_{n-1}` (if the height is `n`).
2. The relation `⋤` should **only care about the indices**.
    That is, only about the outcomes of choices made so far.
    Not about the implementation details of the choices.
    That is: just checking if the 
    choice-outcomes-lists are (propositionally) equal.
    (Ignore things like the proof irrelevant terms for `IsNotMax n`,
    proofs of no forced coercion, etc.).
3. Throw away weeks of work and start over.


## The bad news
* Throw away weeks of work.
* Confused, was still in hyperfocus on the low level details,
    now have to force myself out of this hyperfocus because I realised it was
    the wrong path.

## The good news
1. I learned a lot along the way.
2. Found a much more elegant route to implement all this.
3. **Valuable lessons for science:**
    * Ensure your definition of "sameness" (or "subsequence of choices")
        only cares about the outcomes of the choices, **not** about the
        implementation details of the choices.
    * We will now structure things like this: 
        we have a (indexed family of) type of states.
        The constructors and terms themselves encode implementation
        details of a history of choices.
        Constructors ensure that invariants are maintained when adding a choice,
        (which is much easier than only storing the outcomes of choices,
        writing a function to extend it with a choice, and then
        proving "if the invariants held before then they hold after extending as
        well", which I originally tried but was also very complex)
        But the indices encode the outcomes of the choices, which is all we need
        to compare sequences of choices.
        This is also all we need to check normality, and hence, to extract the
        quotient relation encoded in the choices.

## Lessons learned
* When writing very complicated proofs in which you need to need to trace the
  implementation details about some complicated function and are hoping,
  fingers crossed, that things normalise and hold judgementally,
  **then you should probably take a step back and restructure things such that
  the desired properties are easier available**.
  For example:
    - Let functions also output proofs of invariants.
    - Encode invariants in the type.

* Pawel told some approximately this: 
  this is often how things go. You go through a lot of suffering, then
  start doubting whether this cannot be done better, and then realise how to do
  better. That's how you learn.
