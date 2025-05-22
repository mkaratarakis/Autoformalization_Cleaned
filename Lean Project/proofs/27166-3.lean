import Init.Data.List.Count
import Init.Data.List.MinMax
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.Basic

open List
open Nat

example (n : Nat) (a : α) (l : List α) :
    (leftpad n a l).length = max n l.length := by
  rw [leftpad]
  cases h : decide (n ≤ l.length) with
  | true =>
    rw [dif_pos h]
    simp [length_append, length_replicate, tsub_eq_zero_of_le]
    rfl
  | false =>
    rw [dif_neg (not_le.mp h)]
    simp [length_append, length_replicate, tsub_eq_self_of_gt (not_le.mp h)]
    rw [Nat.sub_add_cancel (le_max_right n l.length)]
    exact max_eq_right (not_le.mp h)

/- ACTUAL PROOF OF List.leftpad_length -/

example (n : Nat) (a : α) (l : List α) :
    (leftpad n a l).length = max n l.length := by
  simp only [leftpad, length_append, length_replicate, Nat.sub_add_eq_max]