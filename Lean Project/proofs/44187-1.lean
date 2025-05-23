import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example {n} (x y : BitVec n) : x - y = x + - y := by
  have h1 : (x - y).toNat = (x + (-y)).toNat := by
    simp [sub_eq_add_neg, toNat_sub, toNat_add, toNat_neg]
    rw [Nat.add_comm]
    rfl
  exact BitVec.eq_of_toNat_eq h1

/- ACTUAL PROOF OF BitVec.sub_toAdd -/

example {n} (x y : BitVec n) : x - y = x + - y := by
  apply eq_of_toNat_eq
  simp
  rw [Nat.add_comm]