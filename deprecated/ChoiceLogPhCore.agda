-- Unused and unfinished lemmas.
-- Some only work in a module whith the same context as `SGStates`
-- in StreamGrids.ChoiceLog.PhCore.
-- The above module might have been renamed by the time you read this.

--------------------------------------------------------------------------------
-- Finished lemmas in context of `SGStates`.
--------------------------------------------------------------------------------

-- In my use case: q' = stripDownTo q i'.
lemma2
    : {n : StateIndices}
    → (i : SIndices)
    → (q' : SGState (cardToSuc i))
    → (j' : iElem q')
    → cardTo≤ {card} (proj₁ j') i
lemma2 i q' (j , h) = card<s→≤ {card} {i} {j} h

lemma4
    : {n : StateIndices}
    → (q : SGState n)
    → (i' : iElem q)
    → (j' : iElem (stripDownTo q i'))
    → (h : (proj₁ j' ≡ proj₁ (lastIdx (stripDownTo q i')))
        ⊎
        (cardTo< (proj₁ j' ) (proj₁ (lastIdx (stripDownTo q i'))))
        )
    → ((proj₁ j' ≡ proj₁ i') ⊎ (cardTo< (proj₁ j') (proj₁ i')))
lemma4 q i' j' h = subst P (lemma3 q i') h
    where
        P = (λ x → (proj₁ j' ≡ x) ⊎ (cardTo< (proj₁ j' ) x))

--------------------------------------------------------------------------------
-- Unfinished lemmas
--------------------------------------------------------------------------------
    cardTo<s
        : {n : ℕ∞}
        → (i : cardToSet n)
        → cardTo< {suc∞ n} (cardInject i) (cardToSuc i)
    cardTo<s i = ?

    cardTo≤Lift
        : {n : ℕ∞}
        → {j i : cardToSet n}
        → (cardTo≤ {n} j i)
        → (cardTo≤ {suc∞ n} (cardInject j) (cardInject i))
    cardTo≤Lift {n} {j} {i} j≤i = ?
    
    -- If j < (suc i) then j ≤ i.
    card<s→≤Lifted
        : {n : ℕ∞} 
        → {i j : cardToSet n} 
        → (cardTo< {suc∞ n} (cardInject j) (cardToSuc i) )
        --^ Note: this < lives in `cardToSet (suc∞ n)`.
        → (cardTo≤ {suc∞ n} (cardInject j) (cardInject i))
    card<s→≤Lifted {n} {i} {j} j<si = ?
