import Init.Data.Array.Lemmas
import Init.Data.List.Impl

open List


example (as : List α) (n : Nat) : as.length + n = as.lengthTRAux n := by
  induction as with
  | nil =>
    simp [length, lengthTRAux]
  | cons a as ih =>
    simp [length, lengthTRAux]
    rw [Nat.add_succ, ih]
    exact Nat.add_comm _ _

/- ACTUAL PROOF OF List.length_add_eq_lengthTRAux -/

example (as : List α) (n : Nat) : as.length + n = as.lengthTRAux n := by
  induction as generalizing n with
  | nil  => simp [length, lengthTRAux]
  | cons a as ih =>
    simp [length, lengthTRAux, ← ih, Nat.succ_add]
    rfl