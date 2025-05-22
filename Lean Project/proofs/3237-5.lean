import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (x n p : Nat) (h₁ : x < n*p) : (n * p - (x + 1)) / n = p - ((x / n) + 1) := by
  have hn : 0 < n := by
    contrapose! h₁
    simp [h₁]
  suffices (n * p - (x + 1)) = n * (p - ((x / n) + 1)) by
    rw [this]
    apply Nat.div_eq_of_lt
    exact hn
  calc
    n * p - (x + 1) = n * p - x - 1 := by rfl
    _ = n * (p - (x / n)) - 1 := by rw [Nat.mul_sub_right_distrib]
    _ = n * (p - (x / n + 1)) := by rw [Nat.sub_sub]

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