# More general signatures are possible
7 March 2026

My signatures allow a finite set of ℕ-indexed families of constructors with the
same (finite) arity. 
Hence it does not allow, for example, a constructors of each arity in ℕ;
but these are still enumerable since only countably many constructors.

Of course, one can still simulate such constructors via an applicative style.
E.g. for lists we have `Cons[a] : List A → List A` for each `a ∈ A`;
lists can have an arbitrary number of arguments, but instead of giving
them all to one constructor we pile them up using multiple constructors:
```agda
Cons[a] (Cons[b] (Cons[c] (Cons[d] Nil)))
```

Either way, it is probably too late now to change everything?
I need to make progress...
