import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (m n : Nat) : n * (m / n) + m % n = m := by
  simp only [Nat.div_eq_ite, Nat.mod_eq_ite]
  cases' h : Decidable (0 < n ∧ n ≤ m) with
  | false =>
    simp only [h, ite_false]
  | true =>
    have hn : 0 < n := by simp only [h, true_and]
    have hnm : n ≤ m := by simp only [h, and_true]
    simp only [h, ite_true, Nat.one_mul, one_add, tsub_add_cancel_of_le hnm]
    apply Nat.mul_add_right_cancel
    apply Nat.add_sub_cancel_right
    simp only [Nat.mul_add_right_cancel]
    simp only [Nat.add_sub_cancel_right]
    simp only [Nat.mul_add_right_cancel]
    simp only [Nat.add_sub_cancel_right]

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