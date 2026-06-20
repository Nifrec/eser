# Forest relations
*Some thoughts of Lulof Pirée , 20 June 2026*

In the first paper I conjectured in the future work that it is not specifically 
enumerability, but the existence of a forest-shaped relation `_<_` on a type `A`
that we need to be able to define normalisation functions `A → A`
by which we can quotient. Because then the laws `f a ≤ a` and `f (f a) ≡ f a`
still ensure there is one equivalence class with a canonical representative,
which is a fixpoint of `f`.

The only reason why I have not put I high priority on this, is that
I fail to come up with any type that:
1. Is not already enumerable.
2. But does have a forest-shaped relation.
3. Has decidable equality.

## Forest-shaped relations: decidable equality without enumerability?
If `A` has decidable equality and is non-enumerable and non-totally-ordered,
then `List A` has a forest-shaped relation `_<_` with `xs < ys` iff `ys` is an
extension of `xs`. If `a, a' : A` are nonequal elements
then `a ∷ xs` and `a' ∷ xs` are incomparable, but both bigger than `xs`.
So we obtain a forest shaped relation.

But do there exist non-enumerable types with decidable equality?
Intuitively, every term we can build is ultimately a parse-tree of constructors
with arguments applied (esp. when also regarding `λ`-abstractions and induction
principles as syntactic constructors),
and a decider just checks if parse trees are equal.

## Canonicity
The problem seems to be that types like `ℕ → Bool` "don't have canonicity",
by which I mean we cannot pattern-match their terms.
This allows more models to validate the type theory.
However, when not interested in categorical semantics,
then I would expect every term in `ℕ → Bool` to be constructed from
either `λ` or `ℕ-ind`. 

I suspect there are close connections between:
* Enumerability
* Canonicity (being-able-to-pattern-match)
* Decidable equality

Of course, *Enumerability => Decidable equality*. 
I have no idea how one could construct the reverse implication though.

I guess *Canonicity => Enumerability ∧ Decidable equality*
since finite parse-trees over a finite alphabet of constructors can be compared
and enumerated.

## My plans
As discussed in my midterm report, I aim to construct a type theory based on
STAMs (generalised CA) as the next project.
I have some sketches for syntactic representations of local rules[^1]
that ensure function in- and ex-tensionality at the same time.
If things work out as I hope, then this will give canonical function types
that can be pattern-matched to a local rule.


[^1]: Which is intuitively obviously possible, 
  since local rules are just finite tables --
  only some care is needed to avoid the existence of different encodings
  for the same local rule.
