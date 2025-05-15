import Init.Omega
import Init.Data.Nat.Mod

open Nat


example (a0 : 0 < a) : a * b < a * c ↔ b < c := by
  induction a with
  | zero =>
    simp
    exact fun h => False.elim (not_lt_zero _ h)
  | succ n ih =>
    simp at a0
    cases a0
    simp [Nat.mul_succ, Nat.add_lt_add_iff_left]
    exact ih

/- ACTUAL PROOF OF Nat.mul_lt_mul_left -/

example (a0 : 0 < a) : a * b < a * c ↔ b < c := by
  induction a with
  | zero => simp_all
  | succ a ih =>
    cases a
    · simp
    · simp_all [succ_eq_add_one, Nat.right_distrib]
      omega