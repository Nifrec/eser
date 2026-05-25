# The problem with `TeleTerms`
2 March 2026

`TeleTerms` defines the terms of a term algebra as a stack of Σs and ⊎s,
explicitly tupeling all the choices made in the construction of the term.
Terms are created in rounds, with only a finite number of terms created each
round, and constructors only using arguments from earlier rounds.
This ensures all terms are enumerable, in such a way that arguments to
constructors always receive a smaller number than the complete term itself.

`TeleTerms` can be defined in Agda, but the dependency on earlier rounds
means that the termination checker needs some help.
This can be solved by Well-Founded recursion on ℕ:
```agda
TeleTerms : (S : TerseSignature) → Set
TeleTerms S = Σ[ i ∈ ℕ ] ( round S i )
    where
        kindCaseDistinction : (S : TerseSignature) 
            → (n : ℕ) 
            → ConstrKind 
            → ((m : ℕ) → (m < n) → Set)
            → Set
        round : TerseSignature → ℕ → Set
        round S = <-rec (λ i → Set) 
            (λ i → λ rec → 
            Σ[ ck ∈ ConstrKind ] kindCaseDistinction S i ck rec)

        kindCaseDistinction S i c-pure-nullary rec
            = Σ[ c ∈ Fin (pure-nullary S) ] i ≡ 0
        kindCaseDistinction S i c-ℕ-nullary rec
            = Σ[ c ∈ Fin (ℕ-nullary S) ] Σ[ n ∈ ℕ ] (n < i)
            --^ n < i : value n may only be used in round (suc n).
            -- Note: this forces i > 0, 
            -- so we do not need to store this explicitly.
        kindCaseDistinction S i c-pure-multiary rec 
            = 
            Σ[ hᵢ ∈ i > 0 ] 
            --^ To avoid an α in round 0 constisting of
            -- round 0 elements.
            Σ[ c ∈ indices (pure-multiary S) ]
            Σ[ m ∈ Fin (getArity S (inj₁ c)) ]
            -- α is a vector whose length is ℕ.suc m
            -- which is in the range [1, ..., arity S (inj₁ c)],
            -- whose elements are terms from round (i ∸ 1). 
            -- We use Well-Founded recursion to define `round (i - 1)`.
            Σ[ α ∈ Vec 
                    (rec (Data.Nat.pred i) (0<n⇒pred[n]<n hᵢ) ) -- round (i - 1)
                    (ℕ.suc (toℕ m))
            ] 
            -- β is a vector of length m - |α| (so |α| + |β| ≡ m)
            -- with elements from `round 0 ⊎ round 1 ⊎ ... ⊎ round (i ∸ 2).
            -- Note that α and β do not share elements,
            -- and their union always contains at least one element
            -- from round (i ∸ 1). β can be empty.
            Σ[ β ∈ Vec 
                (Σ[ j ∈ ℕ ] Σ[ hⱼ ∈ ℕ.suc (ℕ.suc j) < i ] rec j (ssn<m⇒n<m hⱼ)) 
                (getArity S (inj₁ c) ∸ Data.Vec.length α) 
            ]
            VMerging α β
        -- Same as previous case, but now also an n < i,
        -- which in turn makes hᵢ redundent (it guarrantees i > 0
        -- otherwise no such n exists).
        kindCaseDistinction S i c-ℕ-multiary rec
            = 
            Σ[ n ∈ ℕ ] 
            Σ[ hₙ ∈ n < i ] 
            Σ[ c ∈ indices (ℕ-multiary S) ]
            Σ[ m ∈ Fin (getArity S (inj₂ c)) ]
            Σ[ α ∈ Vec 
                (rec (Data.Nat.pred i) (0<n⇒pred[n]<n (m<n⇒0<n {n} {i} hₙ)) ) 
                (ℕ.suc (toℕ m)) 
            ]
            Σ[ β ∈ Vec 
                (Σ[ j ∈ ℕ ] Σ[ hⱼ ∈ ℕ.suc (ℕ.suc j) < i ] rec j (ssn<m⇒n<m hⱼ))
                ((getArity S (inj₂ c)) ∸ Data.Vec.length α)
            ]
            VMerging α β
```

## What's the problem?
I got very far with this, but then got stuck at the following: the types of
arguments, which are the elements in α and β, to a term in round `i+1`
should have type `round i` (and for β: `round k` for `k < i`).
However, the type that Agda really sees is a black-box type-level 
call to Well-Founded recursion. 
Maybe it can be proven that this call is `≡` to `round i`,
but that seems tricky, complicated and not so elegant.

This is a problem when trying to destruct free terms:
to make the map `TerseFreeTerms → TeleTerms`,
I managed to compute the rounds of the arguments of the input term,
but I did not know how to tell Agda that this ensures they are of the types
defined via the WF-recursive-call. 

## What's the solution?
Make `Round S : ℕ → Set` an indexed inductive type.
Instead of Well-Founded recursion we can now simply use inductive arguments,
which not only make the termination checker happy
but also ensure arguments really have an explicit type of the form `Round i`.
Making it easier to define `decomposeTerm : TerseFreeTerms → TeleTerms`,
*I hope.* 
(I've been working on this function already quite a long time, 
but here I got stuck).
