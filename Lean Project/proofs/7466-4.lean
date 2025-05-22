import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example (n) (a : α) : rotateRight (replicate m a) n = replicate m a := by
  induction n with
  | zero =>
    simp [rotateRight]
  | succ k ih =>
    simp [rotateRight]
    have h : 1 < m := by
      apply Nat.succ_le_of_lt
      exact zero_lt_succ m
    rw [Nat.add_sub_cancel_left, Nat.mod_lt, Nat.min_eq_left]
    . exact Nat.mod_lt _ h
    . exact Nat.le_add_right _ _
    . exact Nat.le_add_right _ _
    simp [ih]

/- ACTUAL PROOF OF List.rotateRight_replicate -/

example (n) (a : α) : rotateRight (replicate m a) n = replicate m a := by
  cases n with
  | zero => simp
  | succ n =>
    suffices 1 < m → m - (m - (n + 1) % m) + min (m - (n + 1) % m) m = m by
      simpa [rotateRight]
    intro h
    have : (n + 1) % m < m := Nat.mod_lt _ (by omega)
    rw [Nat.min_eq_left (by omega)]
    omega