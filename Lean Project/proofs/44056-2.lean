import Init.Data.Bool
import Init.Data.BitVec.Basic
import Init.Data.Fin.Lemmas
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Mod
import Init.Data.Int.Bitwise.Lemmas
import Init.Data.BitVec.Lemmas

open BitVec


example (x : BitVec w) : x.msb = true ↔ 2 * x.toNat ≥ 2^w := by
    constructor
    · intro h
      rw [msb_eq_true_iff_not_false] at h
      rw [msb_eq_false_iff_lt_pow] at h
      push_neg at h
      exact h
    · intro h
      by_contra contra_h
      have h1 := msb_eq_false_iff_lt_pow.2 contra_h
      linarith

/- ACTUAL PROOF OF BitVec.msb_eq_true_iff_two_mul_ge -/

example (x : BitVec w) : x.msb = true ↔ 2 * x.toNat ≥ 2^w := by
  simp [← Bool.ne_false_iff, msb_eq_false_iff_two_mul_lt]