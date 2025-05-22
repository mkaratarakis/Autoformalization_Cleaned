import Init.Data.List.Sublist
import Init.Data.List.Pairwise

open List
open Nat

example (p : α → Prop) [DecidablePred p] {l : List α} :
    Pairwise R (filter p l) ↔ Pairwise (fun x y => p x → p y → R x y) l := by
  have : ∀ x, Option.guard (p x) = if h : p x then some x else none := by
    intro x
    cases h : decide (p x) <;> simp [Option.guard, h]
  simp only [filterMap_eq_filter, this, Pairwise, List.bind, List.mem_bind, Option.isSome, exists_and_right, exists_eq_right]
  rw [← forall_swap]
  simp only [and_imp, forall_apply_eq_imp_iff]
  apply forall_congr
  intro x
  apply forall_congr
  intro y
  apply forall_congr
  intro h
  simp [Option.guard] at h
  assumption

/- ACTUAL PROOF OF List.pairwise_filter -/

example (p : α → Prop) [DecidablePred p] {l : List α} :
    Pairwise R (filter p l) ↔ Pairwise (fun x y => p x → p y → R x y) l := by
  rw [← filterMap_eq_filter, pairwise_filterMap]
  simp