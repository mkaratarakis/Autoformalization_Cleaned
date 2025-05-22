import Init.Data.Bool
import Init.Data.Int.Pow
import Init.Data.Nat.Bitwise.Basic
import Init.Data.Nat.Lemmas
import Init.Data.Nat.Simproc
import Init.TacticsExtra
import Init.Omega
import Init.Data.Nat.Bitwise.Lemmas

open Nat


example {x : Nat} (lt : x < 2^n) : x &&& 2^n-1 = x := by
  rw [← Nat.mod_eq_of_lt lt]
  rw [← mod_add_div x (2^n)]
  rw [Nat.mul_ite_of_lt]
  rw [mod_and]
  rfl

/- ACTUAL PROOF OF Nat.and_pow_two_identity -/

example {x : Nat} (lt : x < 2^n) : x &&& 2^n-1 = x := by
  rw [and_pow_two_is_mod]
  apply Nat.mod_eq_of_lt lt