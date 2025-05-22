import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x y : BitVec n) : x.toInt ≠ y.toInt ↔ x ≠ y := by
  constructor
  · intro h
    contrapose! h
    exact toInt_inj h
  · intro h
    contrapose! h
    exact toInt_inj h

/- ACTUAL PROOF OF BitVec.toInt_ne -/

example (x y : BitVec n) : x.toInt ≠ y.toInt ↔ x ≠ y := by
  rw [Ne, toInt_inj]