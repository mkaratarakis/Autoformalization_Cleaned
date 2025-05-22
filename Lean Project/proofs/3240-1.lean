import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (m n k : Nat) : m / n / k = m / (n * k) := by
  by_cases hk : k = 0
  · simp [hk]
  by_cases hn : n = 0
  · simp [hn]
  have h1 : m / n / k * (n * k) ≤ m := by
    rw [mul_comm, mul_assoc]
    apply Nat.div_mul_le_self
  have h2 : m / (n * k) * k ≤ m / n := by
    rw [mul_comm, mul_assoc]
    apply Nat.div_mul_le_self
  exact le_antisymm h1 h2

/- ACTUAL PROOF OF Nat.div_div_eq_div_mul -/

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