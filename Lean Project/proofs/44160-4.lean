import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x y z : BitVec n) : x + y + z = x + (y + z) := by
  have h1 : (x.toNat + y.toNat) + z.toNat = x.toNat + (y.toNat + z.toNat) := Nat.add_assoc _ _ _
  rw [←toNat_inj]
  exact h1

/- ACTUAL PROOF OF BitVec.add_assoc -/

example (x y z : BitVec n) : x + y + z = x + (y + z) := by
  apply eq_of_toNat_eq ; simp [Nat.add_assoc]