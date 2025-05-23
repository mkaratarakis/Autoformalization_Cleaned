import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x y z : BitVec n) : x + y + z = x + (y + z) := by
  rw [← ofNat_eq_ofNat_iff]
  rw [Nat.add_assoc]

/- ACTUAL PROOF OF BitVec.add_assoc -/

example (x y z : BitVec n) : x + y + z = x + (y + z) := by
  apply eq_of_toNat_eq ; simp [Nat.add_assoc]