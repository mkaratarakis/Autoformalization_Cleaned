import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example : 0 ≤ sign x ↔ 0 ≤ x := by
  by_cases h : 0 ≤ x
  · -- Case 2: x = 0
    by_cases h' : x = 0
    · -- x = 0
      simp [h']
      exact ⟨le_rfl, le_rfl⟩
    -- x ≠ 0
    have : x = succ n := exists_eq_succ_of_nat_ne_zero (by_contradiction (hx : x = 0); exact h' (Ne.symm hx))
    simp [this, sign_of_pos (le_of_lt (succ_pos n))]
    exact ⟨le_rfl, le_of_lt (succ_pos n)⟩
  · -- Case 1: x < 0
    rcases exists_eq_neg_succ_of_neg h with ⟨n, hn⟩
    simp [hn, sign_of_neg (succ_pos n)]
    exact ⟨not_le_of_gt (neg_succ_lt_zero n), not_le_of_gt h⟩

/- ACTUAL PROOF OF Int.sign_nonneg -/

example : 0 ≤ sign x ↔ 0 ≤ x := by
  match x with
  | 0 => rfl
  | .ofNat (_ + 1) =>
    simp (config := { decide := true }) only [sign, true_iff]
    exact Int.le_add_one (ofNat_nonneg _)
  | .negSucc _ => simp (config := { decide := true }) [sign]