import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Range

open List
open Nat

example (l : List α) (n) (i : Nat) (h : i < (zipIdx l n).length) :
    (zipIdx l n)[i] = (l[i]'(by simpa [length_zipIdx] using h), n + i) := by
  have h₁ : i < l.length := by simpa [length_zipIdx] using h
  have h₂ : (zipIdx l n)[i] = Option.get (Option.map (fun a => (a, n + i)) (l[i]?)) := by
    rw [List.zipIdx_get?]
    simp [h₁]
  have h₃ : l[i]? = some (l[i]'(by assumption)) := by simp [h₁]
  rw [h₃] at h₂
  simp at h₂
  exact h₂

/- ACTUAL PROOF OF List.getElem_enumFrom -/

example (l : List α) (n) (i : Nat) (h : i < (l.enumFrom n).length) :
    (l.enumFrom n)[i] = (n + i, l[i]'(by simpa [enumFrom_length] using h)) := by
  simp only [enumFrom_length] at h
  rw [getElem_eq_getElem?]
  simp only [getElem?_enumFrom, getElem?_eq_getElem h]
  simp