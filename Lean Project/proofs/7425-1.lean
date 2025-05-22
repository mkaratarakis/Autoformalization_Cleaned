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
  simp only [get?_eq_some']
  -- Construct the elements `x` and `y`
  exists l[i]'(lt_length_left_of_zipWith h), l'[i]'(lt_length_right_of_zipWith h)
  -- Prove the required equalities
  constructor
  · exact get?_eq_some'.2 (lt_length_left_of_zipWith h)
  · exact get?_eq_some'.2 (lt_length_right_of_zipWith h)
  · rfl

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