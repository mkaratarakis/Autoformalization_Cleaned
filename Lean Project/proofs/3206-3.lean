import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (x : Nat) {z : Nat} (H : 0 < z) : (x + z) / z = (x / z) + 1 := by
  have h1 : x + z = z + x := by simp
  rw [h1]
  have h2 : z + x / z = (x / z) + 1 := by
    have t1 : 0 < x + z := lt_of_lt_of_le H (le_add_right _ _)
    have t2 : z ≤ x + z := le_add_right _ _
    have t3 : (x + z) - z = x := by simp
    rw [Nat.div_eq_of_lt t1]
    rw [t3]
    simp
  rw [h2]

/- ACTUAL PROOF OF Nat.add_div_right -/

example (x : Nat) {z : Nat} (H : 0 < z) : (x + z) / z = (x / z) + 1 := by
  rw [div_eq_sub_div H (Nat.le_add_left _ _), Nat.add_sub_cancel]