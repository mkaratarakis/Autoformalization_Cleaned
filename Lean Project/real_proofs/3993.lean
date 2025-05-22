import Init.Data.Nat.Div
import Init.Meta
import Init.Data.Nat.Dvd

open Nat



example (a : Nat) (h : c ∣ b) : a % b % c = a % c := by
  rw (config := {occs := .pos [2]}) [← mod_add_div a b]
  have ⟨x, h⟩ := h
  subst h
  rw [Nat.mul_assoc, add_mul_mod_self_left]