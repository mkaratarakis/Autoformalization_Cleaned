import Init.Classical
import Init.ByCases




example {P : Prop} [Decidable P] {A : P → α} :
    (dite P A fun _ => b) = b ↔ ∀ h, A h = b := by
  constructor
  · intro h
    by_cases hp : P
    · have : dite P A (fun x => b) = A hp := by simp [hp]
      rw [this] at h
      exact fun h' => h
    · have : dite P A (fun x => b) = b := by simp [hp]
      rw [this] at h
      exact h
  · intro h
    by_cases hp : P
    · have : dite P A (fun x => b) = A hp := by simp [hp]
      rw [this]
      exact h hp
    · have : dite P A (fun x => b) = b := by simp [hp]
      rw [this]
      exact rfl

/- ACTUAL PROOF OF dite_eq_right_iff -/

example {P : Prop} [Decidable P] {A : P → α} :
    (dite P A fun _ => b) = b ↔ ∀ h, A h = b := by
  by_cases P <;> simp [*, forall_prop_of_true, forall_prop_of_false]