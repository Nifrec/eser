# Where I left off on 27 Feb:

I was proving 

compileMembershipMapCongr
    : {A B : Set}
    → {α β : List A} 
    → (m : Merging α β)
    → (f : A → B)
    → (b : B)
    → b ∈ map f (compileMerging m) 
    → (b ∈ map f α) ⊎ (b ∈ map f β)
-- Informal proof sketch:
-- First get pre-img a of b, then use compileMembership, and then elim that.
-- Don't case distinct on m. Prove sidelemma b ∈ map f L -> a ∈ L × f a ≡ b.
-- From a ∈ L we get a ∈ α ⊎ a ∈ β. Hence b ≡ f a is then in α or β as well.
-- QED.

because I needed it to finish showing |maxes| > 0 to get m, which
is the predecessor of |maxes|, which is one of the data points
of a TeleTerm. 

There are also more holes in Signatures to fill.
Maybe first check if big picture still makes sense to prove the above!

Then also reverse-max-presv lemma.

## 1 March 2026 update
Data.List.Membership.Setoid.Properties has
```agda
  ∈-map⁻ : ∀ {v xs f} → v ∈₂ map f xs →
           ∃ λ x → x ∈₁ xs × v ≈₂ f x
  ∈-map⁻ x∈map = find (Any.map⁻ x∈map)
```
so use this with `(≡-setoid _)` to get the first part of my strategy.
