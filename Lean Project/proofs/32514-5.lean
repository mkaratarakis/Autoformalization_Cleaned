import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (h : n ≠ 0) : k ≤ n.log2 ↔ 2 ^ k ≤ n := by
  induction k with
  | zero =>
    constructor
    · intro h0
      exact zero_le _
    · intro h0
      exact le_of_lt (one_le_pow_two_iff_pos.2 h)
  | succ k ih =>
    by_cases hle : n < 2
    · constructor
      · intro h0
        exfalso
        exact Nat.not_succ_le_zero _ h0
      · intro h0
        exfalso
        exact lt_irrefl _ ((Nat.lt_of_not_ge hle).trans_le h0)
    · rw [log2_succ h]
      constructor
      · intro h0
        apply ih.1
        simpa using h0
      · intro h0
        apply ih.2
        simpa using h0

/- ACTUAL PROOF OF Nat.le_log2 -/

example (h : n ≠ 0) : k ≤ n.log2 ↔ 2 ^ k ≤ n := by
  match k with
  | 0 => simp [show 1 ≤ n from Nat.pos_of_ne_zero h]
  | k+1 =>
    rw [log2]; split
    · have n0 : 0 < n / 2 := (Nat.le_div_iff_mul_le (by decide)).2 ‹_›
      simp only [Nat.add_le_add_iff_right, le_log2 (Nat.ne_of_gt n0), le_div_iff_mul_le,
        Nat.pow_succ]
      exact Nat.le_div_iff_mul_le (by decide)
    · simp only [le_zero_eq, succ_ne_zero, false_iff]
      refine mt (Nat.le_trans ?_) ‹_›
      exact Nat.pow_le_pow_of_le_right Nat.zero_lt_two (Nat.le_add_left 1 k)