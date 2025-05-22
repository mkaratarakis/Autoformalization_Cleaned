import Init.Data.Bool
import Init.Data.Int.Pow
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc
import Init.TacticsExtra
import Init.Omega
import Init.Data.Nat.Bitwise.Lemmas

open Nat



example (x y i : Nat) : (x &&& y).testBit i = (x.testBit i && y.testBit i) := by
  simp [HAnd.hAnd, AndOp.and, land, testBit_bitwise ]