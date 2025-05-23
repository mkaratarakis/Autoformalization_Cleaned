import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x y : BitVec n) (h1 : x <= y) (h2 : ¬ x = y) : x < y := by
  have : x.toNat < y.toNat := by
  have : x.toNat ≤ y.toNat := h1
  have : ¬ x.toNat = y.toNat := h2
  apply Nat.lt_of_le_of_ne this this
  rw [BitVec.val_toNat]
  exact this
  rw [BitVec.lt_def, BitVec.toNat_eq_val]
  exact Nat.lt_of_le_of_ne this this

/- ACTUAL PROOF OF BitVec.lt_of_le_ne -/

example (x y : BitVec n) (h1 : x <= y) (h2 : ¬ x = y) : x < y := by
  revert h1 h2
  let ⟨x, lt⟩ := x
  let ⟨y, lt⟩ := y
  simp
  exact Nat.lt_of_le_of_ne