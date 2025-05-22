import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example {n k : Nat} (hLtN : 0 < n) (hLtK : 1 < k) : n / k < n := by
  cases h : 0 < k ∧ k ≤ n
  · -- Case where the condition is false
    simp [Nat.div_eq_zero_of_lt]
    exact hLtN
  · -- Case where the condition is true
    rcases h with ⟨hLtK', hKN⟩
    have hDivLe : (n - k) / k ≤ n - k := by
      apply Nat.div_le_self_of_le_one
      exact Nat.le_of_lt hLtK
    have hAddLe : (n - k) / k + k ≤ n := by
      apply Nat.add_le_add_left
      exact hDivLe
    have hLt : (n - k) / k + 1 < n := by
      apply Nat.lt_of_lt_of_le
      exact Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_le hAddLe)
      exact hLtK
    exact hLt

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