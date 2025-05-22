import Init.Data.Bool
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc

open Nat
open Simproc



example (a c : Nat) {b d : Nat} (h : b ≤ d) : a + b - (c + d) = a - (c + (d-b)) := by
  induction b generalizing a c d with
  | zero =>
    simp
  | succ b ind =>
    match d with
    | 0 =>
      contradiction
    | d + 1 =>
      have g := Nat.le_of_succ_le_succ h
      rw [Nat.add_succ a, Nat.add_succ c, Nat.succ_sub_succ, Nat.succ_sub_succ,
          ind _ _ g]