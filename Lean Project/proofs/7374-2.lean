import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example (L : List α) {j i} :
    get (L.take j) i =
    get L ⟨i.1, Nat.lt_of_lt_of_le i.2 (length_take_le' _ _)⟩ := by
  cases' h : L with hd tl
  · simp
  rw [take]
  split
  · exact zero_lt_succ _
  · rw [get, length_take, length_cons]
    apply lt_of_succ_lt_succ
    exact h
  unfold get
  simp only [take, get, length_take, length_cons, Nat.lt_of_lt_of_le, Nat.succ_ne_zero, and_true, not_false_iff, Nat.zero_lt_succ, length, get, Nat.succ_eq_add_one, zero_add] at *
  sorry

/- ACTUAL PROOF OF List.get_take' -/

example (L : List α) {j i} :
    get (L.take j) i =
    get L ⟨i.1, Nat.lt_of_lt_of_le i.2 (length_take_le' _ _)⟩ := by
  simp [getElem_take']