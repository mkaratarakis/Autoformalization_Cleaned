import Init.Data.Nat.Dvd
import Init.NotationExtra
import Init.RCases
import Init.Data.Nat.Gcd

open Nat


example (n : Nat) : gcd n 0 = n := by
  induction n with
  | zero =>
    -- Base case: n = 0
    rfl
  | succ k ih =>
    -- Inductive step: assume gcd k 0 = k, show gcd (k + 1) 0 = k + 1
    rw [gcd_succ_right_self]
    rfl

/- ACTUAL PROOF OF Nat.gcd_zero_right -/

example (n : Nat) : gcd n 0 = n := by
  cases n with
  | zero => simp [gcd_succ]
  | succ n =>
    -- `simp [gcd_succ]` produces an invalid term unless `gcd_succ` is proved with `id rfl` instead
    rw [gcd_succ]
    exact gcd_zero_left _