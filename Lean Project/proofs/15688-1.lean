import Init.Prelude
import Init.SizeOf
import Init.Core


variable {α : Sort u}
variable {a b : α} {p : Prop}
variable {a b : α} {p : Prop}
variable {α β φ : Sort u} {a a' : α} {b b' : β} {c : φ}

example {α β : Sort u} {a : α} {b : β} (h₁ : α = β) (h₂ : Eq.rec (motive := fun α _ => α) a h₁ = b) : HEq a b := by
  rw [h₁] at h₂
  exact HEq.rec h₂
  done

/- ACTUAL PROOF OF heq_of_eqRec_eq -/

example {α β : Sort u} {a : α} {b : β} (h₁ : α = β) (h₂ : Eq.rec (motive := fun α _ => α) a h₁ = b) : HEq a b := by
  subst h₁
  apply heq_of_eq
  exact h₂