import Init.Data.Bool
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc

open Nat
open Simproc


example {a b c d : Nat} (p : (a = b) = (c = d)) : (a != b) = (c != d) := by
  simp [p]
  rfl

/- ACTUAL PROOF OF Nat.Simproc.bneEqOfEqEq -/

example {a b c d : Nat} (p : (a = b) = (c = d)) : (a != b) = (c != d) := by
  simp only [bne, beqEqOfEqEq p]