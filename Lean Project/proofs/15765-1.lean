import Init.Data.Bool
import Init.Data.Int.Pow
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc
import Init.TacticsExtra
import Init.Omega
import Init.Data.Nat.Bitwise.Lemmas

open Nat


example {x i : Nat} (lt : x < 2^i) : x.testBit i = false := by
  by_cases h : x.testBit i = true
  · exact Nat.not_lt_of_ge (Nat.testBit_iff_ge.2 h) lt
  · exact h

/- ACTUAL PROOF OF Nat.testBit_lt_two_pow -/

example {x i : Nat} (lt : x < 2^i) : x.testBit i = false := by
  match p : x.testBit i with
  | false => trivial
  | true =>
    exfalso
    exact Nat.not_le_of_gt lt (testBit_implies_ge p)