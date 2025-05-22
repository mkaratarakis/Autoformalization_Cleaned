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
        apply False.elim
        exact Option.noConfusion h
      · intro h
        apply False.elim
        exact Option.noConfusion h
    · apply Iff.intro
      · intro h
        exists h
        rw [Option.get_of_isSome]
        rw [h]
      · intro h
        apply Option.some_inj
        exists h
        rw [Option.get_of_isSome]

/- ACTUAL PROOF OF Option.eq_some_iff_get_eq -/

example : o = some a ↔ ∃ h : o.isSome, o.get h = a := by
  cases o <;> simp