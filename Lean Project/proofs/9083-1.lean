import Init.Data.Fin.Lemmas
import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Pairwise

open List


example (h : l' <+ l) : ∃ is : List (Fin l.length),
    l' = map (get l) is ∧ is.Pairwise (· < ·) := by
  have h : ∃ is : List Nat, l' = map (l ·.get ·) is ∧ is.Pairwise (· < ·) := by
    apply Sublist.recOn h
    · intro h
      use []
      simp [h]
    · intro l' _ ih h
      rcases ih with ⟨is, rfl, h⟩
      use 0 :: map (· + 1) is
      simp
      split <;> simp
    · intro l' _ ih h
      rcases ih with ⟨is, rfl, h⟩
      use is
      simp
      split <;> simp
  rcases h with ⟨is, rfl, h⟩
  use is.map Fin.mk, h
  simp [Fin.mk_eq_val]

/- ACTUAL PROOF OF List.sublist_eq_map_get -/

example (h : l' <+ l) : ∃ is : List (Fin l.length),
    l' = map (get l) is ∧ is.Pairwise (· < ·) := by
  simpa using sublist_eq_map_getElem h