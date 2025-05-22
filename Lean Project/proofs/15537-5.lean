import Init.Omega
import Init.Data.Nat.Mod

open Nat


example {a b c : Nat} (h : a * b < a * c) : b < c := by
  by_cases a0 : a = 0
  · exfalso
    rw [a0] at h
    apply Nat.not_lt_zero
  · have ha : a ≠ 0 := fun hn => a0 (Eq.symm hn)
    exact Nat.mul_lt_mul_left ha h

/- ACTUAL PROOF OF Nat.lt_of_mul_lt_mul_left -/

example {a b c : Nat} (h : a * b < a * c) : b < c := by
  cases a <;> simp_all