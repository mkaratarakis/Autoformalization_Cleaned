import Init.Data.Fin.Lemmas
import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Pairwise

open List



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