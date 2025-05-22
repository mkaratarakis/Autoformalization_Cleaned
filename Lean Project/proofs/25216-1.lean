import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option


example {o : Option α} {a b} : o.getD a = b ↔ (o = some b ∨ o = none ∧ a = b) := by

  cases o
  · -- Case 1: o = none
    simp [getD]
    constructor
    · intro h
      right
      constructor
      · rfl
      · assumption
    · intro h
      cases h
      · contradiction
      · assumption
  · -- Case 2: o = some val
    intro val
    simp [getD]
    constructor
    · intro h
      left
      apply some.inj
      assumption
    · intro h
      cases h
      · assumption
      · contradiction

/- ACTUAL PROOF OF Option.getD_eq_iff -/

example {o : Option α} {a b} : o.getD a = b ↔ (o = some b ∨ o = none ∧ a = b) := by
  cases o <;> simp