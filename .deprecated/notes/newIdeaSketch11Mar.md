# New idea of signature representation & enumerating them
After today's meeting, a new idea came up, and I'm enthusiastic about it!:

## New encoding of signatures
Lazy lists (streams that may end)
s.t. the element at index i gives the number of constructors of arity i.
Constructors in the first lazy list don't take a natural number as argument,
those in the second list do.
```agda
Signature : Type
Signature = LList ℕ × LList ℕ
```

Why not `LList ℕ∞`? (ℕ∞ is ℕ extended with ∞)
Because in my new enumeration idea,
I want to cover ALL constructors in round i with arity ≤ i.
Which is kinda hard if there are infinitely many of them...

## New enumeration idea:
* A term constructed in round i has 'cost' 1 + i.
* A natural number argument n has cost n.
In round i we construct all pairs of constructors and arguments
such that the total cost of the arguments is exactly i.
Note that we don't need to consider constructors with arity greater than i.

* Obviously every combination occurs in **at most one round**,
    because it is too cheap for later rounds and too expensive for 
    earlier rounds.
* But also every combination occurs in **at least one round**,
    this requires inductive reasoning.
    The nullary ones (with argument 0) in round 0,
    unary ones with inductive-arguments from round 0 (and ℕ-argument 0)
    and nullary ones with ℕ-argument 1 in round 1, etc.
    Can inductively see all subterms occur in some finite round.
