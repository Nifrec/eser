-- Stuff previously in Eser/Definitions.agda

-- Really local version of NFLeq : assume previous outputs are OK
-- already (f m ≤ m for all m < n), only check the last one (i.e., f n ≤ n).
NFLeqReallyLoc : LocProp
NFLeqReallyLoc 0 [] = ⊤
NFLeqReallyLoc (ℕ.suc n) v = last v ≤ n
