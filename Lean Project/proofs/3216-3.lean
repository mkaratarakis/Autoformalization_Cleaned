import Init.WF
import Init.WFTactics
import Init.Data.Nat.Basic
import Init.Data.Nat.Div

open Nat


example (m k : Nat) : m % k + k * (m / k) = m := by
  induction m with
  | zero =>
    simp
  | succ m ih =>
    by_cases h : 0 < k ∧ k ≤ m
    · have : k * (m / k + 1) = k * (m / k) + k := by rw [mul_succ]
      simp
      rw [Nat.add_assoc, this, ih]
    · simp [h]

/- ACTUAL PROOF OF Nat.mod_add_div -/

example (m k : Nat) : m % k + k * (m / k) = m := by
  induction m, k using mod.inductionOn with rw [div_eq, mod_eq]
  | base x y h => simp [h]
  | ind x y h IH => simp [h]; rw [Nat.mul_succ, ← Nat.add_assoc, IH, Nat.sub_add_cancel h.2]