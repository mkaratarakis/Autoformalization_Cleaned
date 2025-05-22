import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (x n p : Nat) (h₁ : n*p ≤ x) : (x - n*p) / n = x / n - p := by
  induction p with
  | zero =>
    simp
  | succ p ih =>
    have : n * p ≤ x - n := by
      apply Nat.le_sub_left_of_add_le
      · simp [mul_add, mul_comm]
      · exact Nat.le_add_right h₁
    rw [Nat.mul_succ, Nat.sub_sub, Nat.sub_self, Nat.div_sub_div_cancel_left]
    exact ih this

/- ACTUAL PROOF OF Nat.sub_mul_div -/

example (x n p : Nat) (h₁ : n*p ≤ x) : (x - n*p) / n = x / n - p := by
  match eq_zero_or_pos n with
  | .inl h₀ => rw [h₀, Nat.div_zero, Nat.div_zero, Nat.zero_sub]
  | .inr h₀ => induction p with
    | zero => rw [Nat.mul_zero, Nat.sub_zero, Nat.sub_zero]
    | succ p IH =>
      have h₂ : n * p ≤ x := Nat.le_trans (Nat.mul_le_mul_left _ (le_succ _)) h₁
      have h₃ : x - n * p ≥ n := by
        apply Nat.le_of_add_le_add_right
        rw [Nat.sub_add_cancel h₂, Nat.add_comm]
        rw [mul_succ] at h₁
        exact h₁
      rw [sub_succ, ← IH h₂, div_eq_sub_div h₀ h₃]
      simp [Nat.pred_succ, mul_succ, Nat.sub_sub]