import Init.Data.Bool
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc

open Nat
open Simproc


example (a : Nat) {b c : Nat} (h : c > a) : (a = b + c) = False := by
  intro h'
  rw [h']
  apply Nat.not_le_of_gt
  exact h
  apply Nat.le_add_right

/- ACTUAL PROOF OF Nat.Simproc.eq_add_gt -/

example (a : Nat) {b c : Nat} (h : c > a) : (a = b + c) = False := by
  rw [@Eq.comm Nat a (b + c)]
  exact add_eq_gt b h