import Init.Data.Bool
import Init.Data.Nat.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc

open Nat
open Simproc


example {a b c d : Nat} (p : (a = b) = (c = d)) : (a == b) = (c == d) := by
  unfold beq
  rw [Prod.mk.inj_iff]
  exact p

/- ACTUAL PROOF OF Nat.Simproc.beqEqOfEqEq -/

example {a b c d : Nat} (p : (a = b) = (c = d)) : (a == b) = (c == d) := by
  simp only [Bool.beq_eq_decide_eq, p]