-- #TODO: remove
module FailedTerseFreeTermsVersion {S : TerseSignature} where
    -- `a « t` iff t is build as a contructor with (among others) argument a.
    _«_ : Rel (TerseFreeTerms S) 0ℓ
    a « mk-pure-nullary _ = ⊥           --^ Nullary terms have no argument.
    a « mk-ℕ-nullary _ _ = ⊥            --^ Nullary terms have no argument.
    a « mk-pure-multiary c L = a ∈ L    --^ L is the list of arguments.
    a « mk-ℕ-multiary c L _ = a ∈ L     --^ L is the list of arguments.

    -- The 'subterm' relation is the transitive closure of _«_.
    _«*_ : Rel (TerseFreeTerms S) 0ℓ
    _«*_ = TransClosure _«_ 

    «-WellFounded : WellFounded _«_
    «-WellFounded t = acc f
        where
            f : {k : TerseFreeTerms S} → k « t → Acc _«_ k
            f {k} k∈Lt = ?

    «*-WellFounded : WellFounded _«*_
    «*-WellFounded = TransWellFounded _«_ «-WellFounded

    open TerseSignature

    -- The height of a term is 0 for nullary constructors and otherwise
    -- 1 + (max height of an argument).
    height : TerseFreeTerms S → ℕ
    height (mk-pure-nullary _)    = 0
    height (mk-ℕ-nullary _ _)     = 0
    --height (mk-pure-multiary c L) = ℕ.suc (max 0 (map height (toList L)))
    height (mk-pure-multiary c (x ∷ L)) = ℕ.suc (height x)
    height (mk-ℕ-multiary c (x ∷ L) _) = ℕ.suc (height x)
    --height (mk-ℕ-multiary c L _)  = ℕ.suc (max 0 (map height (toList L)))


    --termsAcc : {h : ℕ} → (t : TerseFreeTerms S) → (height t ≡ h) → Acc _«_ t
    --termsAcc {h} t height≡h = acc ?
