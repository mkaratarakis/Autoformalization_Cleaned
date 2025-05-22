import Init.Classical
import Init.ByCases




example [Decidable P] {x : P → α} {y : α} :
    (if h : P then some (x h) else none) = some y ↔ ∃ h : P, x h = y := by
  constructor
  · intro h1
    by_cases hp : P
    · use hp
      rw [dif_pos hp] at h1
      exact Option.some.inj h1
    · rw [dif_neg hp] at h1
      exact h1
  · rintro ⟨hp, rfl⟩
    rw [dif_pos hp]
    rfl

/- ACTUAL PROOF OF dite_some_none_eq_some -/

example [Decidable P] {x : P → α} {y : α} :
    (if h : P then some (x h) else none) = some y ↔ ∃ h : P, x h = y := by
  by_cases h : P <;> simp [h]