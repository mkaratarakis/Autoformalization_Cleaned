import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat

example (h : (f a).isNone) : findSome? f (replicate n a) = none := by
  rw [findSome?_replicate]
  cases n
  ·
  {
    rw [Nat.zero_ne_succ]
    rw [dif_neg]
    rw [h]
  }
  ·
  {
    rw [Nat.succ_ne_zero]
    rw [dif_pos]
    rw [h]
  }

/- ACTUAL PROOF OF List.find?_replicate_of_isNone -/

example (h : (f a).isNone) : findSome? f (replicate n a) = none := by
  rw [Option.isNone_iff_eq_none] at h
  simp [findSome?_replicate, h]