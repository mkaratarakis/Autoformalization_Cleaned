import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat

example (p : α → Bool) (b : α) (l : List α) :
    (b :: l).findIdx p = bif p b then 0 else (l.findIdx p) + 1 := by
  by_cases h : p b = true
  · simp [findIdx, findIdx.go, h]
  · simp [findIdx, findIdx.go, h]
    exact findIdx_go_succ p l 0

/- ACTUAL PROOF OF List.findIdx_cons -/

example (p : α → Bool) (b : α) (l : List α) :
    (b :: l).findIdx p = bif p b then 0 else (l.findIdx p) + 1 := by
  cases H : p b with
  | true => simp [H, findIdx, findIdx.go]
  | false => simp [H, findIdx, findIdx.go, findIdx_go_succ]
where
  findIdx_go_succ (p : α → Bool) (l : List α) (n : Nat) :
      List.findIdx.go p l (n + 1) = (findIdx.go p l n) + 1 := by
    cases l with
    | nil => unfold findIdx.go; exact Nat.succ_eq_add_one n
    | cons head tail =>
      unfold findIdx.go
      cases p head <;> simp only [cond_false, cond_true]
      exact findIdx_go_succ p tail (n + 1)