import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example {f : α → β → γ} {l : List α} {l' : List β}
    {i : Nat} {h : i < (zipWith f l l').length} :
    (zipWith f l l')[i] =
      f (l[i]'(lt_length_left_of_zipWith h))
        (l'[i]'(lt_length_right_of_zipWith h)) := by
  -- Transform the goal using the injectivity of the `some` constructor and the equivalence between element retrieval with a valid index and optional element retrieval.
  have hl := lt_length_left_of_zipWith h
  have hr := lt_length_right_of_zipWith h
  rw [get?_eq_some hl, get?_eq_some hr]
  rfl

/- ACTUAL PROOF OF List.getElem_zipWith -/

example {f : α → β → γ} {l : List α} {l' : List β}
    {i : Nat} {h : i < (zipWith f l l').length} :
    (zipWith f l l')[i] =
      f (l[i]'(lt_length_left_of_zipWith h))
        (l'[i]'(lt_length_right_of_zipWith h)) := by
  rw [← Option.some_inj, ← getElem?_eq_getElem, getElem?_zipWith_eq_some]
  exact
    ⟨l[i]'(lt_length_left_of_zipWith h), l'[i]'(lt_length_right_of_zipWith h),
      by rw [getElem?_eq_getElem], by rw [getElem?_eq_getElem]; exact ⟨rfl, rfl⟩⟩