import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example (n) (a : α) : rotateLeft (replicate m a) n = replicate m a := by
  induction n with
  | zero =>
    simp [rotateLeft]
  | succ n ih =>
    simp [rotateLeft]
    rw [Nat.mod_eq_of_lt]
    by_cases h : 1 < m
    · rw [Nat.sub_add_cancel (Nat.lt_trans h (Nat.lt_of_succ_lt_succ (Nat.lt_of_succ_lt_succ (Nat.zero_lt_succ _))))]
      rw [Nat.mod_eq_of_lt (Nat.lt_of_succ_lt_succ (Nat.zero_lt_succ _))]
      rw [Nat.add_sub_cancel_left]
      rfl
    · rw [Nat.mod_eq_of_lt]
      simp
      rfl

/- ACTUAL PROOF OF List.rotateLeft_replicate -/

example (n) (a : α) : rotateLeft (replicate m a) n = replicate m a := by
  cases n with
  | zero => simp
  | succ n =>
    suffices 1 < m → m - (n + 1) % m + min ((n + 1) % m) m = m by
      simpa [rotateLeft]
    intro h
    rw [Nat.min_eq_left (Nat.le_of_lt (Nat.mod_lt _ (by omega)))]
    have : (n + 1) % m < m := Nat.mod_lt _ (by omega)
    omega