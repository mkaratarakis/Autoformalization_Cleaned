import Init.Data.List.Zip
import Init.Data.Nat.Lemmas
import Init.Data.List.Nat.TakeDrop

open List
open Nat

example {l : List α} {n : Nat} (h : l.drop n ≠ []) :
    (l.drop n).head h = l[n]'(by simp_all) := by
  have hn : n < l.length := by
    apply Nat.lt_of_le_of_ne
    · apply Nat.le_of_not_gt
      intro h1
      apply h
      rw [drop_eq_nil_iff]
      apply Nat.le_of_lt_succ
      exact h1
    · intro h1
      apply h
      rw [h1]
  cases l
  · contradiction
  · cases n
    · simpa
    · rw [head_cons, drop_cons, nthLe_cons _ _ (Nat.lt_of_succ_lt_succ hn), drop_cons _ _ (Nat.succ_pos _)]

/- ACTUAL PROOF OF List.head_drop -/

example {l : List α} {n : Nat} (h : l.drop n ≠ []) :
    (l.drop n).head h = l[n]'(by simp_all) := by
  have w : n < l.length := length_lt_of_drop_ne_nil h
  simpa [head?_eq_head, getElem?_eq_getElem, h, w] using head?_drop l n