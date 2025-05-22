import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {x k n : Nat} (h₁ : n*k ≤ x) : (x - n*k) % n = x % n := by
  induction k with
  | zero =>
    simp
  | succ k h =>
    have h₂ : n * k ≤ x := by
      apply Nat.le_trans
      . exact Nat.le_add_right (n * k) n
      . assumption
    have h₃ := h h₂
    have h₄ : x - n * k ≥ n := by
      apply Nat.le_of_add_le_left
      . rw [Nat.add_comm, Nat.mul_succ]
      . assumption
    rw [Nat.mul_succ, Nat.sub_sub, h₃]
    simp [Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt h₄ (Nat.zero_lt_succ n))]

/- ACTUAL PROOF OF Nat.sub_mul_mod -/

example {x k n : Nat} (h₁ : n*k ≤ x) : (x - n*k) % n = x % n := by
  match k with
  | 0 => rw [Nat.mul_zero, Nat.sub_zero]
  | succ k =>
    have h₂ : n * k ≤ x := Nat.le_trans (le_add_right _ n) h₁
    have h₄ : x - n * k ≥ n := by
      apply Nat.le_of_add_le_add_right (b := n * k)
      rw [Nat.sub_add_cancel h₂]
      simp [mul_succ, Nat.add_comm] at h₁; simp [h₁]
    rw [mul_succ, ← Nat.sub_sub, ← mod_eq_sub_mod h₄, sub_mul_mod h₂]