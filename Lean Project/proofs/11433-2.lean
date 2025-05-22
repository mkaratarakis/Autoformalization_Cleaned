import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases
import Init.Data.Nat.Gcd

open Nat


example (m n k : Nat) : gcd (m * n) (m * k) = m * gcd n k := by
  induction n with
  | zero =>
    simp [gcd, Nat.zero_mul]
  | succ n ih =>
    rw [Nat.succ_eq_add_one, Nat.mul_succ, Nat.mul_succ]
    rw [Nat.gcd_rec (m * n) (m * k)]
    rw [ih]
    rw [Nat.gcd_rec (m * (n.gcd k)) (m * (k % n))]
    rw [Nat.mul_mod]
    rw [Nat.gcd_mul_left]
    rfl

/- ACTUAL PROOF OF Nat.gcd_mul_left -/

example (m n k : Nat) : gcd (m * n) (m * k) = m * gcd n k := by
  induction n, k using gcd.induction with
  | H0 k => simp
  | H1 n k _ IH => rwa [← mul_mod_mul_left, ← gcd_rec, ← gcd_rec] at IH