import Init.Data.Nat.MinMax
import Init.Data.Nat.Log2
import Init.Data.Nat.Power2
import Init.Omega
import Init.Data.Nat.Lemmas

open Nat


example {a n m : Nat} (h : 1 < a) (w : n < m) : a ^ n < a ^ m := by
  have : ∃ k, m = n + k + 1 := by
    exists (m - n - 1)
    rw [Nat.sub_add_cancel (Nat.le_of_lt w)]
  rcases this with ⟨k, rfl⟩
  rw [Nat.add_assoc]

  rw [pow_add]
  rw [pow_add]
  rw [pow_add]
  rw [Nat.mul_assoc]

  apply mul_lt_mul
  · apply one_lt_pow_of_one_lt h
  · apply zero_lt_pow
    apply zero_lt_one_add
    assumption

/- ACTUAL PROOF OF Nat.pow_lt_pow_of_lt -/

example {a n m : Nat} (h : 1 < a) (w : n < m) : a ^ n < a ^ m := by
  have := Nat.exists_eq_add_of_lt w
  cases this
  case intro k p =>
  rw [Nat.add_right_comm] at p
  subst p
  rw [Nat.pow_add, ← Nat.mul_one (a^n)]
  have t : 0 < a ^ k := Nat.pow_pos (Nat.lt_trans Nat.zero_lt_one h)
  exact Nat.mul_lt_mul_of_lt_of_le (Nat.pow_lt_pow_succ h) t t