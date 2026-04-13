# Why we represent signatures this particular way in Agda

We index signatures by the cardinality of nullary constructors μ and 
of 1+-ary constructors ζ, so that we can deduce the cardinality of
the term algebra of a signature `S` already from its type `S : Signature μ ζ`.
(μ = 0 -> empty, ζ = 0 -> term algebra same size as nullary,
μ,ζ > 0 -> term algebra isomorphic to ℕ).

For the same reasoning we separate nullary and 1+-ary constructors;
giving just a ℕ → ℕ function giving the arities
(or more generally, a `cardToSet γ → ℕ` function for some cardinality γ of
constructors) makes it undecidable to check if the term algebra is inhabited or
not; the task of checking whether a nullary constructor exist becomes
impossible.
