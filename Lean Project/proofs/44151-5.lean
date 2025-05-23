import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example {n} (x y : BitVec n) : x - y = .ofNat n ((2^n - y.toNat) + x.toNat) := by
  rw [sub_def, ofNat_def]
  simp [toNat_def, Nat.mod_def, Nat.add_mod]
  rw [Nat.add_comm, Nat.add_assoc]
  rw [Nat.mod_eq_of_lt]
  simp

/- ACTUAL PROOF OF BitVec.sub_def -/

example {n} (x y : BitVec n) : x - y = .ofNat n ((2^n - y.toNat) + x.toNat) := by
  rfl