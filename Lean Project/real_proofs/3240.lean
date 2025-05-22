import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat



example (m n k : Nat) : m / n / k = m / (n * k) := by
  cases eq_zero_or_pos k with
  | inl k0 => rw [k0, Nat.mul_zero, Nat.div_zero, Nat.div_zero] | inr kpos => ?_
  cases eq_zero_or_pos n with
  | inl n0 => rw [n0, Nat.zero_mul, Nat.div_zero, Nat.zero_div] | inr npos => ?_

  apply Nat.le_antisymm

  apply (le_div_iff_mul_le (Nat.mul_pos npos kpos)).2
  rw [Nat.mul_comm n k, ← Nat.mul_assoc]
  apply (le_div_iff_mul_le npos).1
  apply (le_div_iff_mul_le kpos).1
  (apply Nat.le_refl)

  apply (le_div_iff_mul_le kpos).2
  apply (le_div_iff_mul_le npos).2
  rw [Nat.mul_assoc, Nat.mul_comm n k]
  apply (le_div_iff_mul_le (Nat.mul_pos kpos npos)).1
  apply Nat.le_refl