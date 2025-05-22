import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option


example : x.map f = some b ↔ ∃ a, x = some a ∧ f a = b := by
  constructor
  · intro h
    cases hx : x <;> simp at h
    · exfalso
      exact h
    · exists hx
  · rintro ⟨a, rfl, rfl⟩
    simp

/- ACTUAL PROOF OF Option.map_eq_some' -/

example : x.map f = some b ↔ ∃ a, x = some a ∧ f a = b := by
  cases x <;> simp