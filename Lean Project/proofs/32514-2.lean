import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (h : n ≠ 0) : k ≤ n.log2 ↔ 2 ^ k ≤ n := by
  induction k with
  | zero =>
    simp [log2]
    exact ⟨fun h0 => by simp [h0], fun h0 => by simp [h0]⟩
  | succ k ih =>
    by_cases hle : n < 2
    · simp [hle]
      exact ⟨fun h0 => by simp [h0], fun h0 => by simp [h0]⟩
    · have h₁ : n / 2 < n := Nat.div_lt_of_lt_mul hle
      have h₂ : n / 2 ≠ 0 := ne_of_gt h₁
      rw [log2_succ h]
      simp
      exact ⟨fun h0 => by simp [ih.mp (le_of_succ_le_succ h0)], fun h0 => by simp [ih.mpr (Nat.div_le_of_le_mul h0)]⟩

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