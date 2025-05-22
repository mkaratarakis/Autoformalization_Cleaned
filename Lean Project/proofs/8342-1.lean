import Init.Data.Bool
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc

open Nat
open Simproc


example {a b : Nat} (p : (a = b) = False) : (a == b) = false := by
  -- Start from the definition of boolean equality
  unfold beq
  -- Simplify using the definition of decide
  simp [decide]
  -- Apply the assumption that a = b is false
  rw [p]
  -- Simplify to obtain the result
  simp

/- ACTUAL PROOF OF Nat.Simproc.beqFalseOfEqFalse -/

example {a b : Nat} (p : (a = b) = False) : (a == b) = false := by
  simp [Bool.beq_eq_decide_eq, p]