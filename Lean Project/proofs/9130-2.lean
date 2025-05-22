import Init.Data.Fin.Lemmas
import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Pairwise

open List


example : Pairwise R l ↔
    ∀ (i j : Nat) (_hi : i < l.length) (_hj : j < l.length) (_hij : i < j), R l[i] l[j] := by
  constructor
  · intro h i j _hi _hj _hij
    have h1 : ∀ i, i < l.length → l.get ⟨i, _hi⟩ = l[i] := by
      intro i hi
      rfl
    have h2 : ∀ j, j < l.length → l.get ⟨j, _hj⟩ = l[j] := by
      intro j hj
      rfl
    exact h (h1 i _hi) (h2 j _hj) _hij
  · intro h
    apply Pairwise.of_get
    intros a b ha hb hab
    obtain ⟨is, his⟩ := exists_indices_of_sublist
    cases is
    · constructor
    · constructor
    · constructor
    · exact his
    · exact h (is.get ⟨a, ha⟩) (is.get ⟨b, hb⟩) (his a ha) (his b hb) (hab a b ha hb)

/- ACTUAL PROOF OF List.pairwise_iff_getElem -/

example : Pairwise R l ↔
    ∀ (i j : Nat) (_hi : i < l.length) (_hj : j < l.length) (_hij : i < j), R l[i] l[j] := by
  rw [pairwise_iff_forall_sublist]
  constructor <;> intro h
  · intros i j hi hj h'
    apply h
    simpa [h'] using map_getElem_sublist (is := [⟨i, hi⟩, ⟨j, hj⟩])
  · intros a b h'
    have ⟨is, h', hij⟩ := sublist_eq_map_getElem h'
    rcases is with ⟨⟩ | ⟨a', ⟨⟩ | ⟨b', ⟨⟩⟩⟩ <;> simp at h'
    rcases h' with ⟨rfl, rfl⟩
    apply h; simpa using hij