import Init.Data.Bool
import Init.Data.Int.Pow
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc
import Init.TacticsExtra
import Init.Omega
import Init.Data.Nat.Bitwise.Lemmas

open Nat


example (x : Nat) : x &&& 0 = 0 := by
  unfold bundledBand
  unfold homogeneousBand
  unfold band
  simp [Nat.zero_eq]
  simp [Nat.zero_eq]
  simp

/- ACTUAL PROOF OF Nat.and_zero -/

example (x : Nat) : x &&& 0 = 0 := by
  simp only [HAnd.hAnd, AndOp.and, land]
  unfold bitwise
  simp