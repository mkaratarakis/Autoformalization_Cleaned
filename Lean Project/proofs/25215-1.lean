import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option


example : x.bind f = some b ↔ ∃ a, x = some a ∧ f a = some b := by
  constructor
  · intro h
    cases x <;> simp at h
    · contradiction
    · exact ⟨x_val, rfl, h⟩
  · rintro ⟨a, rfl, h⟩
    cases x <;> simp
    · contradiction
    · rw [h]

/- ACTUAL PROOF OF Option.bind_eq_some -/

example : x.bind f = some b ↔ ∃ a, x = some a ∧ f a = some b := by
  cases x <;> simp