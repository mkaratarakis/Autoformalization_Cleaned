import Init.Data.Int.Lemmas
import Init.ByCases
import Init.Data.Int.Order

open Int
open Nat

example {a b : Int} : a < b ↔ a ≤ b ∧ ¬b ≤ a := by
  rw [lt_iff_le_and_ne]
  rw [and_congr_right_iff]
  intro h
  constructor
  · exact h.left
  · intro hba
    apply h.right
    exact le_antisymm h.left hba

/- ACTUAL PROOF OF Int.lt_iff_le_not_le -/

example {a b : Int} : a < b ↔ a ≤ b ∧ ¬b ≤ a := by
  rw [Int.lt_iff_le_and_ne]
  constructor <;> refine fun ⟨h, h'⟩ => ⟨h, h'.imp fun h' => ?_⟩
  · exact Int.le_antisymm h h'
  · subst h'; apply Int.le_refl