import Init.Data.List.Sublist
import Init.Data.List.Pairwise

open List
open Nat

example (p : α → Prop) [DecidablePred p] {l : List α} :
    Pairwise R (filter p l) ↔ Pairwise (fun x y => p x → p y → R x y) l := by
  rw [← filterMap_eq_filter _ p]
  simp only [Option.guard, filterMap, Pairwise, List.bind]
  simp only [List.mem_bind, Option.isSome]
  simp only [exists_and_right, exists_eq_right]
  rw [← forall_swap]
  simp only [and_imp, forall_apply_eq_imp_iff]

/- ACTUAL PROOF OF List.pairwise_filter -/

example (p : α → Prop) [DecidablePred p] {l : List α} :
    Pairwise R (filter p l) ↔ Pairwise (fun x y => p x → p y → R x y) l := by
  rw [← filterMap_eq_filter, pairwise_filterMap]
  simp