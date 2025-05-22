import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example (n : Nat) : Nodup (range n) := by
  rw [range_eq_range']
  cases n with
  | zero => simp [Nodup]
  | succ n =>
    simp [Nodup]
    apply nodup_cons
    · intro i hi
      cases i with
      | zero => exact Nat.zero_ne_succ _ hi
      | succ j =>
        rw [range'_succ] at hi
        exact Nat.succ.inj_ne hi
    · apply nodup_range'

/- ACTUAL PROOF OF List.nodup_range -/

example (n : Nat) : Nodup (range n) := by
  simp (config := {decide := true}) only [range_eq_range', nodup_range']