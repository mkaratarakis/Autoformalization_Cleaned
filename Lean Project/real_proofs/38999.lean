import Init.Classical
import Init.ByCases





example {P : Prop} [Decidable P] {B : ¬ P → α} :
    dite P (fun _ => a) B = a ↔ ∀ h, B h = a := by
  by_cases P <;> simp [*, forall_prop_of_true, forall_prop_of_false]