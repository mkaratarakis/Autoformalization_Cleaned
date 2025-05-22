import Init.Classical
import Init.ByCases




example (f : α → β) (P : Prop) [Decidable P] (x : P → α) (y : ¬P → α) :
    f (dite P x y) = dite P (fun h => f (x h)) (fun h => f (y h)) := by
  by_cases hp : P
  · let h := hp
    simp [dite_eq_ite, if_pos hp, h]
  · let h := hp
    simp [dite_eq_ite, if_neg hp, h]

/- ACTUAL PROOF OF apply_dite -/

example (f : α → β) (P : Prop) [Decidable P] (x : P → α) (y : ¬P → α) :
    f (dite P x y) = dite P (fun h => f (x h)) (fun h => f (y h)) := by
  by_cases h : P <;> simp [h]