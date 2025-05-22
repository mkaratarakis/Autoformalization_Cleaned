import Init.Omega
import Init.Data.Nat.Mod

open Nat


example {a b c : Nat} (h : a * b < a * c) : b < c := by
  by_cases a0 : a = 0
  · exfalso
    rw [a0] at h
    exact Nat.not_lt_zero _ h
  · have ha : a ≠ 0 := fun hn => a0 (hn.symm)
    rw [← one_mul a, ← one_mul b, ← one_mul c] at h
    have hb : (a * b : Nat) < (a * c : Nat) := h
    have hc : (a * b : Nat) = (a * b : Nat) := rfl
    rw [mul_comm a] at h
    have hd : (a * b : Nat) < (a * c : Nat) := h
    apply Nat.mul_lt_mul_left ha hd

/- ACTUAL PROOF OF Nat.lt_of_mul_lt_mul_left -/

example {a b c : Nat} (h : a * b < a * c) : b < c := by
  cases a <;> simp_all