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
      exact Nat.zero_lt_succ 1
    rw [Nat.sub_eq_add_neg, Nat.add_comm, Nat.sub_add_cancel, Nat.mod_lt, Nat.min_eq_left]
    . exact Nat.mod_lt _ h
    . exact Nat.le_of_lt h
    . exact Nat.le_of_lt h
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