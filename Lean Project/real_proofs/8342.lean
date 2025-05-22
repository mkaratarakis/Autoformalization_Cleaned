import Init.Data.Bool
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc

open Nat
open Simproc



example {a b : Nat} (p : (a = b) = False) : (a == b) = false := by
  simp [Bool.beq_eq_decide_eq, p]