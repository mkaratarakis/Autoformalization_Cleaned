import Init.Data.BitVec.Folds
import Init.Data.Nat.Mod
import Init.Data.BitVec.Bitblast

open BitVec
open Nat Bool

example {x y : BitVec w} (h : x.msb ≠ y.msb) :
    x.ult y = y.msb := by
  have h1 : ¬(2 ^ (w - 1) ≤ x.toNat ↔ 2 ^ (w - 1) ≤ y.toNat) := by
    simp [msb] at h
    rw [← Nat.lt_iff_add_one_le] at h
    exact h
  have h2 : x.toNat < y.toNat ↔ 2 ^ (w - 1) ≤ y.toNat := by
    rw [ult, ← Nat.lt_iff_add_one_le]
    exact h1
  unfold ult
  unfold msb
  rw [h2]

/- ACTUAL PROOF OF BitVec.ult_eq_msb_of_msb_neq -/

example {x y : BitVec w} (h : x.msb ≠ y.msb) :
    x.ult y = y.msb := by
  simp only [BitVec.ult, msb_eq_decide, ne_eq, decide_eq_decide] at *
  omega