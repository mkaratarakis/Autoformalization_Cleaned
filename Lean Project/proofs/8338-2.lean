import Init.Data.Bool
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc

open Nat
open Simproc


example {a b : Nat} (p : (a = b) = False) : (a != b) = true := by
  unfold bne
  rw [beq_eq_dec]
  apply decidable_of_decidable_of_iff
  intro h
  rw [h] at p
  exact False.elim p

/- ACTUAL PROOF OF Nat.Simproc.bneTrueOfEqFalse -/

example {a b : Nat} (p : (a = b) = False) : (a != b) = true := by
  simp [bne, beqFalseOfEqFalse p]