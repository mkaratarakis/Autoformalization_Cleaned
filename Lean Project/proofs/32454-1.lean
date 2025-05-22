import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example (a b n : Nat) : (a + b) % n = ((a % n) + (b % n)) % n := by
  rw [add_mod]
  rfl

/- ACTUAL PROOF OF Nat.add_mod -/

example (a b n : Nat) : (a + b) % n = ((a % n) + (b % n)) % n := by
  rw [add_mod_mod, mod_add_mod]