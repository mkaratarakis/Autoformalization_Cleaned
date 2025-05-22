import Init.Omega
import Init.Data.Nat.Mod

open Nat


example {a b c : Nat} (h : b * a < c * a) : b < c := by
  have h₁ : a ≠ 0 := by
    intro h₂
    exfalso
    apply Nat.not_lt_zero a
    apply lt_of_mul_lt_mul_left h h₂
  have h₂ : a * b < a * c := by
    rw [mul_comm b a, mul_comm c a] at h
    exact h
  exact Nat.mul_lt_mul_left (Nat.pos_of_ne_zero h₁) h₂

/- ACTUAL PROOF OF Nat.lt_of_mul_lt_mul_right -/

example {a b c : Nat} (h : b * a < c * a) : b < c := by
  rw [Nat.mul_comm b a, Nat.mul_comm c a] at h
  exact Nat.lt_of_mul_lt_mul_left h