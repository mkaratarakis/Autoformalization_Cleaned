import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (m n : Nat) : n * (m / n) + m % n = m := by
  simp only [Nat.div_eq_ite, Nat.mod_eq_ite]
  by_cases h : 0 < n ∧ n ≤ m <;> simp [h]
  · simp
  · rw [Nat.div_eq_sub_add_one, Nat.mod_eq_sub]
    have h' : n ≤ m - n := by
      apply Nat.sub_le_sub_right
      apply Nat.le_of_lt
      exact h.2
    simp [Nat.mul_add_right_cancel, Nat.add_sub_cancel_right, h']

/- ACTUAL PROOF OF Nat.div_add_mod -/

example (m n : Nat) : n * (m / n) + m % n = m := by
  rw [div_eq, mod_eq]
  have h : Decidable (0 < n ∧ n ≤ m) := inferInstance
  cases h with
  | isFalse h => simp [h]
  | isTrue h =>
    simp [h]
    have ih := div_add_mod (m - n) n
    rw [Nat.left_distrib, Nat.mul_one, Nat.add_assoc, Nat.add_left_comm, ih, Nat.add_comm, Nat.sub_add_cancel h.2]
decreasing_by apply div_rec_lemma; assumption