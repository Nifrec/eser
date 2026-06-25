

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
