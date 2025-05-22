import Init.SimpLemmas
import Init.Data.Nat.Basic

open Nat


example (n : Nat) : succ n ≠ 0 := by
  intro h
  cases n <;> simp at h

/- ACTUAL PROOF OF Nat.succ_ne_zero -/

example (n : Nat) : succ n ≠ 0 := by
  simp