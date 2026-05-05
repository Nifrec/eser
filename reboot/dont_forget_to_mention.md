# Don't forget to mention in the paper or fix beforehand:
* Now I only used A ≃ ℕ as enumerable types, finite A should also be supported.
* Definable quotient stuff of Li and Hofmann.
* Our way of ℤ vs Li's quotients.
* Commuting triangle of lift: (lift g ∘ [ _ ]) ~ g
* «-rec is only implemented for signatures with inf sizes
* #EXT and #TODOs (put in readme)
* Argument how OpenTerms could be constructed without new inductive type.
* `(ℕ → Bool) / ~` (where `~` denotes homotopy) cannot be constructed 
    because `ℕ → Bool` cannot be enumerated (by a diagonalisation argument).
* Remove all `{-# OPTIONS --allow-unsolved-metas #-}` and use the `safe` pragma.
* Mention as one of selling points that the repr of a class is the shortest,
    *which is particularly nice for representing grids via quotients!*
* Discussion point: we can prove smaller weights have smaller numbers
    and that `a « giveArg t a`. But by the way I implemented things
    it is hard to compare `c(x)` and `c'(y)` if, e.g., `c'` is one heavier than
    `c` but `x` is one heavier than `y` (so that both terms have the same
    weight). **My implementation makes it hard to compare things of the same
    weight.** This could have been avoided, e.g. by adding more indices (giving
    the top-lvl constructor index, or the height, or so) to terms.
* "Standard def of ℤ": how to Rocq, Lean and Li define ℤ?
