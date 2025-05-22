import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (n m : Nat) : n - m ≤ n := by
  induction m with
  | zero =>
    -- Base Case: n - 0 ≤ n
    exact Nat.le_refl n
  | succ m ih =>
    -- Inductive Step: n - (m + 1) ≤ n
    have h1 : n - succ m = pred (n - m) := rfl
    rw [h1]
    apply Nat.le_pred_of_le
    exact ih

/- ACTUAL PROOF OF Nat.sub_le -/

example (n m : Nat) : n - m ≤ n := by
  induction m with
  | zero      => exact Nat.le_refl (n - 0)
  | succ m ih => apply Nat.le_trans (pred_le (n - m)) ih