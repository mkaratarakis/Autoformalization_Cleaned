import Init.Classical
import Init.ByCases





example {P : Prop} [Decidable P] {A : P → α} :
    (dite P A fun _ => b) = b ↔ ∀ h, A h = b := by
  by_cases P <;> simp [*, forall_prop_of_true, forall_prop_of_false]