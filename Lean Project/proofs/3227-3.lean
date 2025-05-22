import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (m n : Nat) : n * (m / n) + m % n = m := by
  by_cases h : n = 0
  · simp [h]
  · have hpos : 0 < n := Nat.pos_of_ne_zero h
    obtain q r hqr := Nat.div_mod_eq m n
    simp [hqr]

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