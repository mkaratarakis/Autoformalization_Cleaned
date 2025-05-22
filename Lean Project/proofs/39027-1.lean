import Init.Classical
import Init.ByCases




example [Decidable P] {x : P → α} {y : α} :
    (if h : P then some (x h) else none) = some y ↔ ∃ h : P, x h = y := by
  constructor
  · intro h1
    by_cases hp : P
    · use hp
      have h2 := congrArg Option.get! h1
      rwa [(Option.get!_eq_iff).mpr hp] at h2
    · exfalso
      rw [dif_neg hp] at h1
      exact Option.noConfusion h1
  · rintro ⟨hp, rfl⟩
    rw [dif_pos hp]
    rfl

/- ACTUAL PROOF OF dite_some_none_eq_some -/

example [Decidable P] {x : P → α} {y : α} :
    (if h : P then some (x h) else none) = some y ↔ ∃ h : P, x h = y := by
  by_cases h : P <;> simp [h]