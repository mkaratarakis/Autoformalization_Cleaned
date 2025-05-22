import Init.Data.Bool
import Init.Data.Int.Pow
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc
import Init.TacticsExtra
import Init.Omega
import Init.Data.Nat.Bitwise.Lemmas

open Nat


example (x : Nat) : 0 &&& x = 0 := by
  unfold &&&
  simp [bitwise_and]
  cases x with
  | zero => simp [bitwise_and]
  | succ x => simp [bitwise_and]

/- ACTUAL PROOF OF Nat.zero_and -/

example (x : Nat) : 0 &&& x = 0 := by
  simp only [HAnd.hAnd, AndOp.and, land]
  unfold bitwise
  simp