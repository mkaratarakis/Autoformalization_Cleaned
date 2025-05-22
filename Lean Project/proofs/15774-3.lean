import Init.Data.Bool
import Init.Data.Int.Pow
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc
import Init.TacticsExtra
import Init.Omega
import Init.Data.Nat.Bitwise.Lemmas

open Nat


example (x : Nat) : testBit (x >>> i) j = testBit x (i+j) := by
  rw [testBit, testBit]
  simp [shiftr_eq_div_pow, Nat.land_eq_mod_pow, Nat.mod_eq_of_lt]

/- ACTUAL PROOF OF Nat.testBit_shiftRight -/

example (x : Nat) : testBit (x >>> i) j = testBit x (i+j) := by
  simp [testBit, ←shiftRight_add]