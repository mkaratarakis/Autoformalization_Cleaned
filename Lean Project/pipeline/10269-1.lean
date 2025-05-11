import Mathlib.Tactic.Ring
import Mathlib.Tactic.Ring

/-!
# Identities

This file contains some "named" commutative ring identities.
-/


variable {R : Type*} [CommRing R] {a b x₁ x₂ x₃ x₄ x₅ x₆ x₇ x₈ y₁ y₂ y₃ y₄ y₅ y₆ y₇ y₈ n : R}

/-- Brahmagupta-Fibonacci identity or Diophantus identity, see
<https://en.wikipedia.org/wiki/Brahmagupta%E2%80%93Fibonacci_identity>.

This sign choice here corresponds to the signs obtained by multiplying two complex numbers.
-/
example :
(x₁ ^ 2 + x₂ ^ 2) * (y₁ ^ 2 + y₂ ^ 2) = (x₁ * y₁ - x₂ * y₂) ^ 2 + (x₁ * y₂ + x₂ * y₁) ^ 2 := by
  rw [mul_add, add_mul, ←add_assoc, ←add_assoc (x₁^2*y₂^2), add_comm (x₂^2*y₁^2), add_assoc, ←sq_sub_sq x₁*y₁ (x₂*y₂),
    ←sq_add x₁*y₂ (x₂*y₁), add_left_comm, ←add_assoc, add_comm (x₁^2*y₂^2), add_left_comm]

/- ACTUAL PROOF OF sq_add_sq_mul_sq_add_sq -/

example :
    (x₁ ^ 2 + x₂ ^ 2) * (y₁ ^ 2 + y₂ ^ 2) = (x₁ * y₁ - x₂ * y₂) ^ 2 + (x₁ * y₂ + x₂ * y₁) ^ 2 := by
  ring