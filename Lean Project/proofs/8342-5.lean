import Init.Data.Bool
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc

open Nat
open Simproc


example {a b : Nat} (p : (a = b) = False) : (a == b) = false := by
  -- Start from the definition of boolean equality
  change decide (a = b)
  -- Simplify using the definition of decide
  rw [decide_eq_false_iff]
  -- Apply the assumption that a = b is false
  exact p

/- ACTUAL PROOF OF Nat.Simproc.beqFalseOfEqFalse -/

example {a b : Nat} (p : (a = b) = False) : (a == b) = false := by
  simp [Bool.beq_eq_decide_eq, p]