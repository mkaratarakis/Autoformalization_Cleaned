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
    · exfalso
      exact ne_of_mem_of_not_mem h (by decide)
    · exact ⟨x_val, rfl, h⟩
  · rintro ⟨a, rfl, h⟩
    simp [bind]
    exact h

/- ACTUAL PROOF OF Option.bind_eq_some -/

example : x.bind f = some b ↔ ∃ a, x = some a ∧ f a = some b := by
  cases x <;> simp