import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example [SizeOf α] (l : List α) (n : Nat) : sizeOf (l.drop n) ≤ sizeOf l := by
  induction l with
  | nil =>
    simp [drop, sizeOf]
  | head tail ih =>
    induction n with
    | zero =>
      simp [drop, sizeOf]
    | succ n ih2 =>
      simp [drop, sizeOf]
      apply Nat.le_trans
      . exact ih2
      . simp
      . exact Nat.le_add_right _ _

/- ACTUAL PROOF OF List.drop_sizeOf_le -/

example [SizeOf α] (l : List α) (n : Nat) : sizeOf (l.drop n) ≤ sizeOf l := by
  induction l generalizing n with
  | nil => rw [drop_nil]; apply Nat.le_refl
  | cons _ _ lih =>
    induction n with
    | zero => apply Nat.le_refl
    | succ n =>
      exact Trans.trans (lih _) (Nat.le_add_left _ _)