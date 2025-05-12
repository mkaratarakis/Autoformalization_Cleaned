import Init.Omega
import Init.Data.Nat.Mod

open Nat


example {a b x : Nat} : x % (a * b) = x % a + a * (x / a % b) := by
  rw [Nat.add_comm]
  rw [Nat.mod_eq_of_lt (Nat.div_lt_iff_pos_of_le (Nat.le_of_lt (Nat.mul_pos_of_ne_of_pos (Nat.ne_of_gt (Nat.one_le_iff_pos.2 (Nat.pos_of_ne_zero x))) (Nat.pos_of_ne_zero a))) (Nat.pos_of_ne_zero b)))]
  rw [Nat.mod_mul_div_mod]
  rfl

/- ACTUAL PROOF OF Nat.mod_mul -/

example {a b x : Nat} : x % (a * b) = x % a + a * (x / a % b) := by
  rw [Nat.add_comm, ← Nat.div_add_mod (x % (a*b)) a, Nat.mod_mul_right_mod,
    Nat.mod_mul_right_div_self]