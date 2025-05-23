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
    -- Case 3: x > 0
    have hx : 0 < x := lt_of_not_ge (by simpa using h')
    simp [sign_eq_ite, hx, if_pos hx]
    exact ⟨le_rfl, h⟩
  · -- Case 1: x < 0
    have hx : x < 0 := not_le.mp h
    simp [sign_eq_ite, hx, if_neg hx]
    exact ⟨not_le_of_gt hx, not_le_of_gt hx⟩

/- ACTUAL PROOF OF Int.sign_nonneg -/

example : 0 ≤ sign x ↔ 0 ≤ x := by
  match x with
  | 0 => rfl
  | .ofNat (_ + 1) =>
    simp (config := { decide := true }) only [sign, true_iff]
    exact Int.le_add_one (ofNat_nonneg _)
  | .negSucc _ => simp (config := { decide := true }) [sign]