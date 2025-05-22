import Init.Data.Bool
import Init.Data.Int.Pow
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc
import Init.TacticsExtra
import Init.Omega
import Init.Data.Nat.Bitwise.Lemmas

open Nat



example (x : Nat) : x ||| 0 = x := by
  simp only [HOr.hOr, OrOp.or, lor]
  unfold bitwise
  simp [@eq_comm _ 0]