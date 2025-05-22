import Init.Omega
import Init.Data.Nat.Mod

open Nat


example {a b c : Nat} (h : a * b < a * c) : b < c := by
  by_cases a0 : a = 0
  · exfalso
    rw [a0] at h
    apply Nat.not_lt_zero
  · have : a ≠ 0 := by
      intro contra
      apply a0
      exact contra.symm
    rw [mul_succ] at h
    exact Nat.lt_of_mul_lt_mul_left this h

/- ACTUAL PROOF OF Nat.lt_of_mul_lt_mul_left -/

example {a b c : Nat} (h : a * b < a * c) : b < c := by
  cases a <;> simp_all