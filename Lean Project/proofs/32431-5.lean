import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a b : Nat) : a - b + b = max a b := by
  cases h : decide (a <= b) with
  | true =>
    rw [Nat.sub_eq_zero_of_le (Nat.le_of_decide_eq_true h)]
    rw [zero_add]
    rw [max_of_le (Nat.le_of_decide_eq_true h)]
  | false =>
    rw [Nat.sub_add_cancel (Nat.not_le_of_decide_eq_false h)]
    rw [max_of_ge (Nat.not_le_of_decide_eq_false h)]

/- ACTUAL PROOF OF Nat.sub_add_eq_max -/

example (a b : Nat) : a - b + b = max a b := by
  match Nat.le_total a b with
  | .inl hl => rw [Nat.max_eq_right hl, Nat.sub_eq_zero_iff_le.mpr hl, Nat.zero_add]
  | .inr hr => rw [Nat.max_eq_left hr, Nat.sub_add_cancel hr]