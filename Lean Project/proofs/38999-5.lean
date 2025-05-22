import Init.Classical
import Init.ByCases




example {P : Prop} [Decidable P] {B : ¬ P → α} :
    dite P (fun _ => a) B = a ↔ ∀ h, B h = a := by
  constructor
  · intro h
    by_cases hp : P
    · have : dite P (fun _ => a) B = a := by simp [hp]
      rw [this] at h
      exact fun h => (h hp).elim
    · have : dite P (fun _ => a) B = B hp := by simp [hp]
      rw [this] at h
      exact fun h => h hp
  · intro h
    by_cases hp : P
    · have : dite P (fun _ => a) B = a := by simp [hp]
      rw [this]
      exact h _
    · have : dite P (fun _ => a) B = B hp := by simp [hp]
      rw [this]
      exact h hp

/- ACTUAL PROOF OF dite_eq_left_iff -/

example {P : Prop} [Decidable P] {B : ¬ P → α} :
    dite P (fun _ => a) B = a ↔ ∀ h, B h = a := by
  by_cases P <;> simp [*, forall_prop_of_true, forall_prop_of_false]