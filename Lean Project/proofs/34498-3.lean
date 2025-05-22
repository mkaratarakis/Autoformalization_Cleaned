import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example {l : List α} {n : Nat} : l.take (n + 1) = l.take n ++ l[n]?.toList := by
  induction l with
  | nil =>
    simp
  | cons hd tl ih =>
    cases n with
    | zero =>
      simp
    | succ m =>
      simp [take, ih]
      rw [ih (m := m)]
      simp [take]

/- ACTUAL PROOF OF List.take_succ -/

example {l : List α} {n : Nat} : l.take (n + 1) = l.take n ++ l[n]?.toList := by
  induction l generalizing n with
  | nil =>
    simp only [take_nil, Option.toList, getElem?_nil, append_nil]
  | cons hd tl hl =>
    cases n
    · simp only [take, Option.toList, getElem?_cons_zero, nil_append]
    · simp only [take, hl, getElem?_cons_succ, cons_append]