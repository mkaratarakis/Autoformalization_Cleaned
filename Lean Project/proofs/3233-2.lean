import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example {n k : Nat} (hLtN : 0 < n) (hLtK : 1 < k) : n / k < n := by
  by_cases hCond : 0 < k ∧ k ≤ n
  · -- Case where the condition is true
    rcases hCond with ⟨_, hKN⟩
    have hDivLe : (n - k) / k ≤ n - k := by
      apply div_le_self
    have hAddLe : (n - k) / k + k ≤ n := by
      apply add_le_add_left
      exact hDivLe
    apply lt_of_lt_of_le
    · apply lt_add_of_pos_right
      exact hKN
    · apply le_of_lt
      apply lt_of_succ_lt_succ
      apply lt_add_of_pos_right
      exact hKN
  · -- Case where the condition is false
    simp [div_eq_zero_of_lt] at hCond
    exact hLtN

/- ACTUAL PROOF OF Nat.div_lt_self -/

example {n k : Nat} (hLtN : 0 < n) (hLtK : 1 < k) : n / k < n := by
  rw [div_eq]
  cases (inferInstance : Decidable (0 < k ∧ k ≤ n)) with
  | isFalse h => simp [hLtN, h]
  | isTrue h =>
    suffices (n - k) / k + 1 < n by simp [h, this]
    have ⟨_, hKN⟩ := h
    have : (n - k) / k ≤ n - k := div_le_self (n - k) k
    have := Nat.add_le_of_le_sub hKN this
    exact Nat.lt_of_lt_of_le (Nat.add_lt_add_left hLtK _) this