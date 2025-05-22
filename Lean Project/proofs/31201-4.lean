import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example {n m k : Nat} (h : n + m = k + m) : n = k := by
  rw [add_comm n m] at h
  rw [add_comm k m] at h
  exact add_left_cancel h

/- ACTUAL PROOF OF Nat.add_right_cancel -/

example {n m k : Nat} (h : n + m = k + m) : n = k := by
  rw [Nat.add_comm n m, Nat.add_comm k m] at h
  apply Nat.add_left_cancel h