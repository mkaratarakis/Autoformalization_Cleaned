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
    apply Nat.lt_of_le_of_ne
    . have hle := (BitVec.toNat_mono h1)
      exact hle
    . intro contra
      apply h2
      apply BitVec.toNat_inj
      exact contra
  rw [BitVec.lt_def]
  exact this

/- ACTUAL PROOF OF BitVec.lt_of_le_ne -/

example (x y : BitVec n) (h1 : x <= y) (h2 : ¬ x = y) : x < y := by
  revert h1 h2
  let ⟨x, lt⟩ := x
  let ⟨y, lt⟩ := y
  simp
  exact Nat.lt_of_le_of_ne