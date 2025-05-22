import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option


example : x.join ≠ none ↔ ∃ z, x = some (some z) := by
  constructor
  · intro h
    by_cases hx : x = none
    · exfalso
      rw [hx] at h
      exact h rfl
    · have hx' : x ≠ none := by simp [hx]
      rcases x with (_ | y)
      · exact hx'
      rcases y with (_ | z)
      · apply False.elim
        exact h rfl
      exists z
  · rintro ⟨z, rfl⟩
    simp [join]

/- ACTUAL PROOF OF Option.join_ne_none -/

example : x.join ≠ none ↔ ∃ z, x = some (some z) := by
  simp only [ne_none_iff_exists', join_eq_some, iff_self]