import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (n k m : Nat) : (n + k) - (m + k) = n - m := by
  induction k with
  | zero =>
    simp
  | succ k' ih =>
    rw [add_succ, add_succ, sub_succ, sub_succ, ih]
    rfl

/- ACTUAL PROOF OF Nat.add_sub_add_right -/

example (n k m : Nat) : (n + k) - (m + k) = n - m := by
  induction k with
  | zero => simp
  | succ k ih => simp [← Nat.add_assoc, succ_sub_succ_eq_sub, ih]