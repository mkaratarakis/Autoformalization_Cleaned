import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} : a < b ↔ a ≤ b ∧ a ≠ b := by
  constructor
  · intro h
    apply And.intro
    · apply Int.le_of_lt
      exact h
    · apply Ne.symm
      apply Int.ne_of_lt
      exact h
  · rintro ⟨h₁, h₂⟩
    exact Int.lt_of_le_of_ne h₁ h₂

/- ACTUAL PROOF OF Int.lt_iff_le_and_ne -/

example {a b : Int} : a < b ↔ a ≤ b ∧ a ≠ b := by
  refine ⟨fun h => ⟨Int.le_of_lt h, Int.ne_of_lt h⟩, fun ⟨aleb, aneb⟩ => ?_⟩
  let ⟨n, hn⟩ := le.dest aleb
  have : n ≠ 0 := aneb.imp fun eq => by rw [← hn, eq, ofNat_zero, Int.add_zero]
  apply lt.intro; rwa [← Nat.succ_pred_eq_of_pos (Nat.pos_of_ne_zero this)] at hn