import Init.Data.Bool
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc

open Nat
open Simproc


example {a b : Nat} (p : (a = b) = False) : (a != b) = true := by
  unfold bne
  simp [beq_iff_eq]
  rw [p]

/- ACTUAL PROOF OF Nat.Simproc.bneTrueOfEqFalse -/

example {a b : Nat} (p : (a = b) = False) : (a != b) = true := by
  simp [bne, beqFalseOfEqFalse p]