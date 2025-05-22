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
    · intro a _ ih h
      rcases ih with ⟨is, rfl, h⟩
      use 0 :: map (· + 1) is
      simp
      constructor
      · rfl
      · exact (Pairwise.cons 0 (map_pairwise _ _ h)).2
    · intro a _ ih h
      rcases ih with ⟨is, rfl, h⟩
      use is
      simp
      constructor
      · rfl
      · exact h
  rcases h with ⟨is, rfl, h⟩
  use is.map (Fin.ofNat ·)
  constructor
  · simp [get, Fin.ofNat_eq_get]
  · exact h.imp fun i j hij => by
      simp at hij
      exact hij

/- ACTUAL PROOF OF List.sublist_eq_map_get -/

example (h : l' <+ l) : ∃ is : List (Fin l.length),
    l' = map (get l) is ∧ is.Pairwise (· < ·) := by
  simpa using sublist_eq_map_getElem h