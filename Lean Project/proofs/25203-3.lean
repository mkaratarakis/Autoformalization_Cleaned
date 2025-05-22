import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option


example : o = some a ↔ ∃ h : o.isSome, o.get h = a := by
  cases o <;> simp
  · apply Iff.intro
    · intro h
      exfalso
      exact Option.noConfusion h
    · intro h
      exfalso
      exact Option.noConfusion h
  · apply Iff.intro
    · intro h
      exists Option.isSome_some
      rw [Option.get_of_isSome]
    · rintro ⟨h, rfl⟩
      exact Option.some_inj.mp h

/- ACTUAL PROOF OF Option.eq_some_iff_get_eq -/

example : o = some a ↔ ∃ h : o.isSome, o.get h = a := by
  cases o <;> simp