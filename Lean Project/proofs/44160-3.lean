import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x y z : BitVec n) : x + y + z = x + (y + z) := by
  have h1 := congrArg ofNat (Nat.add_assoc (ofNat x) (ofNat y) (ofNat z))
  have h2 : ofNat (x + y + z) = ofNat x + ofNat y + ofNat z := by
    rw [←BitVec.add_ofNat, ←BitVec.add_ofNat]
    exact h1
  rw [←ofNat_inj']
  exact h2

/- ACTUAL PROOF OF BitVec.add_assoc -/

example (x y z : BitVec n) : x + y + z = x + (y + z) := by
  apply eq_of_toNat_eq ; simp [Nat.add_assoc]