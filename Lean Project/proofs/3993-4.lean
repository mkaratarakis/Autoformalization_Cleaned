import Init.Data.Nat.Div
import Init.Meta
import Init.Data.Nat.Dvd

open Nat


example (a : Nat) (h : c ∣ b) : a % b % c = a % c := by
  let x := h.witness
  let b_eq: b = c * x := rfl
  rw [b_eq]
  rw [Nat.mod_mul_right_of_dvd (dvd_refl c)]
  rw [Nat.mod_mul_right_of_dvd (dvd_refl c)]

/- ACTUAL PROOF OF Nat.mod_mod_of_dvd -/

example (a : Nat) (h : c ∣ b) : a % b % c = a % c := by
  rw (config := {occs := .pos [2]}) [← mod_add_div a b]
  have ⟨x, h⟩ := h
  subst h
  rw [Nat.mul_assoc, add_mul_mod_self_left]