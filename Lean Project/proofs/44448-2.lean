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
    have : 0 < x := lt_of_le_of_ne h h'
    have hx : x = succ (x - 1) := (succ_sub_one (ne_of_gt this)).symm
    simp [hx, sign_of_pos this]
    exact ⟨le_rfl, le_of_lt this⟩
  · -- Case 1: x < 0
    have : x < 0 := not_le.mp h
    have : x = -succ (-x - 1) := (neg_succ_of_nat_ne_zero (ne_of_gt this)).symm
    simp [this, sign_of_neg (succ_pos (-x - 1))]
    exact ⟨not_le_of_gt (neg_succ_lt_zero (-x - 1)), not_le_of_gt this⟩

/- ACTUAL PROOF OF Int.sign_nonneg -/

example : 0 ≤ sign x ↔ 0 ≤ x := by
  match x with
  | 0 => rfl
  | .ofNat (_ + 1) =>
    simp (config := { decide := true }) only [sign, true_iff]
    exact Int.le_add_one (ofNat_nonneg _)
  | .negSucc _ => simp (config := { decide := true }) [sign]