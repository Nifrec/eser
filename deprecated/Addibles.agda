open import Data.Unit
open import Data.Empty
open import Relation.Binary.PropositionalEquality
open import Data.Nat
open import Data.Nat.Properties
open import Data.Fin
open import Data.Fin.Properties
open import Level

-- Local imports.
open import StreamGrids.Card
open import StreamGrids.Addibles


module deprecated.Addibles where


    IsZero : {c : ℕ} → (a : Fin c) → Set
    IsZero {ℕ.zero} _ = ⊥
    IsZero {ℕ.suc c} Fin.zero = ⊤
    IsZero {ℕ.suc (ℕ.suc c)} (Fin.suc a) = ⊥


    -- #TODO: deprecate function below, it seems useless
    FinAddiblesRecOld
        : {ℓ : Level}
        → (c : ℕ)
        → (i : Fin (ℕ.suc c))
        → (P : (x : ℕ) → Fin x → Set ℓ)
        → ((x : ℕ) → (a : Fin x) → P x a)
        → ((a : Addibles (fin (ℕ.suc c)) i) → P (ℕ.suc c) (add (fin (ℕ.suc c)) i a))
    FinAddiblesRecOld {ℓ} c i P rec a = rec (ℕ.suc c) (add (fin (ℕ.suc c)) i a)
