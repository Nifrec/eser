# Signatures and containers
A signature `S : Signature μ ζ` can also be seen as the least fixpoint
of a a container `(A |> B)`
where `A = (cardToSet µ) ⊎ (cardToSet ζ)` and
```agda
    B (inj₁ c) = ⊤
    B (inj₂ c) = Fin (S c)
```

