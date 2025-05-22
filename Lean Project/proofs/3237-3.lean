import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (x n p : Nat) (h₁ : x < n*p) : (n * p - (x + 1)) / n = p - ((x / n) + 1) := by
  have hn : 0 < n := by
    contrapose! h₁
    simp [h₁]
  calc
    (n * p - (x + 1)) / n = (n * p - (x + 1)) / n := by rfl
    _ = (n * p - (x + 1)) / n := by rfl
    _ = p - ((x / n) + 1) := by
      apply Nat.div_eq_of_lt
      show (p - (x / n + 1)) * n ≤ n * p - (x + 1)
      calc
        (p - (x / n + 1)) * n = p * n - (x / n + 1) * n := by ring
        _ = p * n - (x + n) := by rw [Nat.mul_add, Nat.add_comm]
        _ ≤ p * n - (x + 1) := by
          apply Nat.sub_le_sub_left
          exact Nat.le_add_left _ _
      show n * p - (x + 1) < (p - (x / n + 1) + 1) * n
      calc
        n * p - (x + 1) = n * p - x - 1 := by rw [Nat.sub_sub]
        _ < n * p - x + n - n := by linarith
        _ = n * p - x := by rw [Nat.sub_add_cancel]
        _ = (p - (x / n)) * n := by rw [Nat.sub_mul, Nat.mul_comm]
        _ = (p - (x / n + 1) + 1) * n := by ring

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