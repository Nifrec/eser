# Our signatures are general enough
10 April 2026

## Observation #1
The enumerable W-types are least fixpoints of containers $$(A \triangleright
B)$$ where $$A \leq \mathbb{N}$$ and each $$B a$$ is finite.
After all, if $$B \simeq \mathbb{N}$$ then, assuming the cardinality of the
least fixpoint is at least 2, the cardinality of the whole thing is already
greater than $$\mathbb{N} \to 2$$ which is not enumerable (by a diagonalisation
proof).

## Observation #2
My signatures correspond to such containers.
A signature `S : Signature μ ζ` can also be seen as the least fixpoint
of a a container `(A ▹ B)`
where `A = (cardToSet µ) ⊎ (cardToSet ζ)` and
```agda
    B (inj₁ c) = ⊥
    B (inj₂ c) = Fin (S c)
```
In the reverse direction, if $$(A \triangleright B)$$ is a container with $$A
\leq \mathbb{N}$$ and $$B$$ a family of finite sets,
then it is a signature with $$\mu$$ being the cardinality of $$\{a \in A : B a
\simeq \bot\}$$ and $$\zeta$$ the cardinality of its complement,
with for all `c ∈ cardToSet ζ` we set as arity-minus-one $$S c := | B c | -1$$.

## Conclusion
Up to isomorphism, our representation of signatures is able to capture all
enumerable W-types.
So no worries that my proof isn't general enough...
