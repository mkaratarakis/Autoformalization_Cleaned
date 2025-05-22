import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option


example : x.join ≠ none ↔ ∃ z, x = some (some z) := by
  constructor
  · intro h
    contrapose! h
    simp [join] at h
    exact h
  · rintro ⟨z, rfl⟩
    simp [join]

/- ACTUAL PROOF OF Option.join_ne_none -/

example : x.join ≠ none ↔ ∃ z, x = some (some z) := by
  simp only [ne_none_iff_exists', join_eq_some, iff_self]