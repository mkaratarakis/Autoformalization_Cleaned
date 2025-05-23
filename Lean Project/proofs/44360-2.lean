import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} : a < b ↔ a ≤ b ∧ ¬b ≤ a := by
  constructor
  · intro h
    exact And.intro h (mt (le_antisymm h) (Ne.symm (Ne.of_lt h)))
  · intro h
    exact lt_of_le_of_ne h.1 (mt h.2 le_antisymm h.1)

/- ACTUAL PROOF OF Int.lt_iff_le_not_le -/

example {a b : Int} : a < b ↔ a ≤ b ∧ ¬b ≤ a := by
  rw [Int.lt_iff_le_and_ne]
  constructor <;> refine fun ⟨h, h'⟩ => ⟨h, h'.imp fun h' => ?_⟩
  · exact Int.le_antisymm h h'
  · subst h'; apply Int.le_refl