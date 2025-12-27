-- Lemmas originally posed in StreamGrids/ChoiceLog/IdxAndListCore.agda
-- but that were not used in the end.
-- One could still copy them back and try to finish them if needed.

    -- #TODO: it is possbile to define a 'getWeakSubLog'
    -- where the input is i ≤ (idx q) and the output
    -- is q' ⊑ q (i.o., q' ⋤ q).
    getWeakSubLog
        : (q : Q)
        → (i : C)
        → (i ≤C idx q)
        → Σ[ q' ∈ Q ]( (q' ⋤ q) × (i ≡ idx q'))
    -- #TODO: just remove this function if never needed.
    -- Then also remove _≤C_ !!!
    getWeakSubLog = ? 

    -- #TODO: remove if this does not turn out to be needed,
    -- otherwise finish.
    -- The index-index of a ChoiceLog corresponds 
    -- to the enumeration-index of the last element added.
    elToIdx∘el≡idx
        : (q : Q)
        → elToIdx (el q) ≡ idx q
    elToIdx∘el≡idx (i , L , root h) = {! !}
    elToIdx∘el≡idx (i , L , choose q h lc) = {! !}
        
    
--------------------------------------------------------------------------------
-- Maybe keep, maybe move, maybe remove.
--------------------------------------------------------------------------------
    --next : {n : StateIndices} → IsNotMax n → A
    --next {n} notMax = Signoid.enum S (cardLower notMax)

    --⊑-antisym : Antisymmetric _≡_ _⊑_
    --⊑-antisym {q} {q} (refl q) q⊑q = refl
    --⊑-antisym {q} {q} q⊑q (refl q) = refl
    --⊑-antisym {p} {q} (sub q' p ℓq p⊑q') (sub p' q ℓp q⊑p') = 
    --    let p'⊑p = sub p' p' ℓp (refl p') in
    --    let p'⊑q' = ⊑-trans p'⊑p p⊑q' in
    --    let q'⊑q = sub q' q' ℓq (refl q') in
    --    let q'⊑p' = ⊑-trans q'⊑q q⊑p' in
    --    let p'≡q' = ⊑-antisym p'⊑q' q'⊑p' in
    --     Still need ℓp = ℓq, given that we could
    --     apply cong pm p'≡q' with (λ x → choose x ℓp), and then subst the
    --     right occurrence of ℓp via ℓp=ℓq.
    --    let pℓp≡qℓp = cong (λ x → choose x) p'≡q' (refl (choose p')) in
    --    {!  !}

    -- #TODO: conjecture: Totality and decidability of _⊑_ can also be proven.

