import Init.Omega
import Init.Data.Nat.Mod

open Nat


example {a b c : Nat} (h : b * a < c * a) : b < c := by
  have h₁ : a ≠ 0 := by
    intro h₂
    apply Nat.noConfusion h₂
  have h₂ : a * b < a * c := by
    rwa [mul_comm]
  exact Nat.mul_lt_mul_left h₁ h₂

/- ACTUAL PROOF OF Nat.lt_of_mul_lt_mul_right -/

example {a b c : Nat} (h : b * a < c * a) : b < c := by
  rw [Nat.mul_comm b a, Nat.mul_comm c a] at h
  exact Nat.lt_of_mul_lt_mul_left h