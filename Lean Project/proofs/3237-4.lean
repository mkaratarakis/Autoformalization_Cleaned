import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (x n p : Nat) (h₁ : x < n*p) : (n * p - (x + 1)) / n = p - ((x / n) + 1) := by
  have hn : 0 < n := by
    contrapose! h₁
    simp [h₁]
  have h₂ : n * p - (x + 1) = n * p - x - 1 := by rfl
  have h₃ : (n * p - (x + 1)) / n = (n * p - x - 1) / n := by rw[h₂]
  have h₄ : (n * p - x - 1) / n = p - ((x + 1) / n) := by
    apply Nat.div_eq_of_lt
    calc
      (p - (x + 1) / n) * n ≤ n * p - x - 1 := by
        rw [Nat.mul_sub_right_distrib, Nat.sub_sub, Nat.mul_comm _ n]
        apply Nat.le_sub_left_of_add_le
        apply Nat.le_mul_of_pos_right
        exact Nat.div_lt_of_lt_mul h₁ hn
      n * p - x - 1 < (p - (x + 1) / n + 1) * n := by
        simp [Nat.mul_sub_right_distrib]
        push_cast
        rw [Nat.add_sub_cancel_left]
        rw [Nat.sub_lt_left_iff_add_lt]
        apply Nat.lt_of_mul_lt_mul_left
        exact Nat.div_lt_of_lt_mul h₁ hn
  have h₅ : (n * p - x - 1) / n = p - (x / n + 1) := by
    rw [h₄]
    calc
      p - (x / n + 1) = p - x / n - 1 := by rw [Nat.sub_sub]
      _ = p - (x / n) - 1 := by rw [Nat.sub_sub]
      _ = p - (x / n + 1) := by rfl
  rw [h₃, h₅]

/- ACTUAL PROOF OF Nat.mul_sub_div -/

example (x n p : Nat) (h₁ : x < n*p) : (n * p - (x + 1)) / n = p - ((x / n) + 1) := by
  have npos : 0 < n := (eq_zero_or_pos _).resolve_left fun n0 => by
    rw [n0, Nat.zero_mul] at h₁; exact not_lt_zero _ h₁
  apply Nat.div_eq_of_lt_le
  focus
    rw [Nat.mul_sub_right_distrib, Nat.mul_comm]
    exact Nat.sub_le_sub_left ((div_lt_iff_lt_mul npos).1 (lt_succ_self _)) _
  focus
    show succ (pred (n * p - x)) ≤ (succ (pred (p - x / n))) * n
    rw [succ_pred_eq_of_pos (Nat.sub_pos_of_lt h₁),
      fun h => succ_pred_eq_of_pos (Nat.sub_pos_of_lt h)] -- TODO: why is the function needed?
    focus
      rw [Nat.mul_sub_right_distrib, Nat.mul_comm]
      exact Nat.sub_le_sub_left (div_mul_le_self ..) _
    focus
      rwa [div_lt_iff_lt_mul npos, Nat.mul_comm]