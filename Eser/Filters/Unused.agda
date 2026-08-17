

-- Extend a family B of dependent types from indices in {0, ..., n-1} 
-- to {0, ..., n} by providing B n.
dep-extend
    : (n : ℕ)
    → (B : ℕ → Set)
    → ((m : ℕ) → m < n → B m)
    → B n
    → ((m : ℕ) → m < ℕ.suc n → B m)
dep-extend n B Fam Bn m m<1+n with m Data.Nat.≟ n
... | (yes m≡n) = subst B (sym m≡n) Bn
... | (no m≢n) = Fam m m<n
    where
        open import Data.Nat.Properties using (m<1+n⇒m<n∨m≡n)
        m<n : m < n
        m<n = elimCaseRight (m<1+n⇒m<n∨m≡n m<1+n) m≢n

module _ (T : ReplaceStruct) where
    open ReplaceStructLemmas T

    
    -- If known that `y` has a non-normal argument,
    -- then we know the output of ReplaceRespLocal:
    -- the only allowed choice for the nf of y is
    -- the nf of replace y x x'.
    lemma-ReplaceRespLocal-NonNormalArg-Exence
        : {y x x' : ℕ}
        → (h : (n : ℕ) → NFRestr n)
        → (H : (n : ℕ) → h n ⋖ h (suc n))
        → x ⊂ y
        → x' < x
        → (p : (replace T y x x') < y)
        → AreRelated (h y) x x'
        → Exence-sats ReplaceRespLocal (h , H)
        → getChoiceFromExence (h , H) y ≡ (earlier-new $ resurface (h y) p)
    lemma-ReplaceRespLocal-NonNormalArg-Exence {y} {x} {x'} h H x⊂y x'<x y'<y 
                                               xRx' LocSat 
                                               = decEqReflection _≡?_ LHS RHS K'
        where
            LHS : Choices (h y)
            LHS = getChoiceFromExence (h , H) y

            RHS : Choices (h y)
            RHS = earlier-new $ resurface (h y) y'<y

            F : Filter
            F = ReplaceRespLocal

            K : F (h y) LHS ≡ true
            K = LocSat y

            y' : ℕ
            y' = replace T y x x'

            y'<y-alt : y' < y
            y'<y-alt = replace-< T y x x' x⊂y x'<x

            
            y'<y-alt≡y'<y : y'<y-alt ≡ y'<y
            y'<y-alt≡y'<y = <-irrelevant y'<y-alt y'<y

            -- Compute definition of F, after forcing the output of
            -- the call to `allArgsNormal?`.
            K' : does (LHS ≡? RHS) ≡ true
            K' = sym $
                let (w , w⊂y , w' , w'<w , wRw' , isMin) 
                        = (proj₁ $ lemma-allArgsNormal?-NonNormal (h y) x⊂y 
                                                                  x'<x xRx')
                in
                {! 
                begin 
                    true 
                ≡⟨ sym K ⟩
                    F (h y) LHS
                ≡⟨⟩
                    ReplaceRespLocal-cases (h y) LHS (forgetMinimality $ allArgsNormal? (h y))
                ≡⟨ cong (ReplaceRespLocal-cases (h y) LHS) 
                   $ {! proj₂ $ lemma-allArgsNormal?-NonNormal (h y) x⊂y x'<x xRx' !} ⟩ 
                    --ReplaceRespLocal-cases (h y) LHS (inj₂ (w , w' , w⊂y , w'<w , wRw'))
                    ReplaceRespLocal-cases (h y) LHS (inj₂ (w , w' , w⊂y , w'<w , wRw'))
                    -- (inj₂ (x , x' , x⊂y , x'<x , xRx'))
                    -- #TODO : need to match isNonNormal deeper.
                    -- #TODO: problem: y' does depend on x, not on w.
                    -- This won't work.
                    -- ReplaceRespLocal does call areRelated?,
                    -- and the output of ReplaceRespLocal is all we have.
                    -- 2 options:
                    -- - Somehow get a contradiction when unequal
                    -- - Make `allArgsNormal` come with a proof of being the
                    -- smallest counterexample.
                ≡⟨ ? ⟩ -- Definition ReplaceRespLocal-cases.
                    does (LHS ≡? (earlier-new $ resurface (h y) y'<y-alt))
                    -- Now substitute the proof-irrelevant proof that
                    -- y' < y by the one given.
                ≡⟨ cong (λ p → does (LHS ≡? (earlier-new $ resurface (h y) p)))
                        y'<y-alt≡y'<y ⟩
                    does (LHS ≡? RHS)
                ∎
                !}
    -- Variant of the above lemma in special case where the Exence
    -- is a restrict+-ed normalisation function f.
    -- It carries the result back from an equality on used extension choices
    -- in restrictions of f to an equality on inputs to f.
    -- Implementation note: we don't take an argument z
    -- of type `z : NonNormalArg {y} r` because the output type depends on
    -- the data within z, namely x and x'.
    lemma-ReplaceRespLocal-NonNormalArg-NFFun
        : {y x x' : ℕ}
        → x ⊂ y
        → x' < x
        → (f' : NFFun)
        → AreRelated (restrict f' y) x x'
        → NFFun-sats ReplaceRespLocal f'
        → (proj₁ f' y) ≡ (proj₁ f' (replace T y x x'))
    lemma-ReplaceRespLocal-NonNormalArg-NFFun {y} {x} {x'} x⊂y x'<x 
                                        f'@(f , f-leq , f-fix) xRx' LocSat =
        begin 
            f y    
        ≡⟨⟩
            proj₁ f' y
        ≡⟨ sym $ theo-combine∘restrict+ f' y ⟩
            (proj₁ ∘ combine ∘ restrict+) f' y
        ≡⟨⟩ -- Unfold definition of `combine`:
            (choiceToℕ ∘ (getChoiceFromExence $ restrict+ f')) y
        ≡⟨ cong choiceToℕ forcedChoice ⟩
            choiceToℕ (earlier-new $ resurface (restrict f' y) y'<y)
        ≡⟨⟩ 
            NFSToℕ (resurface (restrict f' y) y'<y)
        ≡⟨ lemma-resurface-getChoice h H y'<y ⟩
            (choiceToℕ ∘ (getChoiceFromExence $ restrict+ f')) y'
        ≡⟨⟩ -- Fold definition `combine`.
            (proj₁ ∘ combine ∘ restrict+) f' y'
        ≡⟨ theo-combine∘restrict+ f' y' ⟩
            proj₁ f' y'
        ≡⟨⟩
            f y' 
        ∎
        where
            y' : ℕ
            y' = replace T y x x'

            y'<y : y' < y
            y'<y = replace-< T y x x' x⊂y x'<x

            h = proj₁ $ restrict+ f'
            H = proj₂ $ restrict+ f'

            forcedChoice : getChoiceFromExence (restrict+ f') y 
                           ≡ 
                           (earlier-new $ resurface (restrict f' y) y'<y)
            forcedChoice = lemma-ReplaceRespLocal-NonNormalArg-Exence
                h H x⊂y x'<x y'<y xRx' LocSat
    -- Given evidence of a non-normal argument, we know the output of
    -- `allArgsNormal?`.
    lemma-allArgsNormal?-NonNormal
        : {y : ℕ}
        → (r : NFRestr y)
        → {x x' : ℕ}
        → (x⊂y : x ⊂ y)
        → (x'<x : x' < x)
        → (xRx' : AreRelated r x x')
        → Σ[ nonNormalArg ∈ MinNonNormalArg r ] allArgsNormal? r ≡ inj₂ nonNormalArg
    lemma-allArgsNormal?-NonNormal {y} r {x} {x'} x⊂y x'<x xRx' = 
        cases (allArgsNormal? r) refl
        where   
            cases
                : (p : AllArgsNormal r ⊎ MinNonNormalArg r)
                → (p ≡ allArgsNormal? r)
                → Σ[ nonNormalArg ∈ MinNonNormalArg r ] allArgsNormal? r ≡ inj₂ nonNormalArg
            cases (inj₁ p) p-eq = ? 
            cases (inj₂ p) p-eq = {! p , sym p-eq !}
                -- use `sym p` and substitute proof-irrelevant stuff
                -- No wait, that might now work, because the witness x
                -- may be different. The lemma should be changed,
                -- to any genereric ` ≡ inj₂ nonNormalArg`, 
                -- but does that break anything?
                --
                -- No, it is only used in K' below, which ignores the data of
                -- the proof anyway.
                -- Fix: let this proof output an unknown `nonNormalArg`
                -- and in that proof with K', also catch this nonNormalArg
                -- and use it in the proof.
