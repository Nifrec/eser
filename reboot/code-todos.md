# TODOs for Agda implementation

* `Eser.Equivalences.Properties`: 
    - `fin-Σ-fun` can by simplified: change the sublemma
        `fin-Σ-takeout-first`
        into
        `→ Σ[ x ∈ Fin (ℕ.suc a) ] B x ≃ B (0) ⊎ Σ[ x ∈ Fin a ] B (suc x)`
        (fewer type casts needed, `fin-Σ-takeout-first` simplifies a lot)
        (Thanks Tarmo).
* Put the ZTheorem in a separate file.
* Prove the basic rewriting ≃-lemmas of Σ types using the functions from the
  stdlib.
