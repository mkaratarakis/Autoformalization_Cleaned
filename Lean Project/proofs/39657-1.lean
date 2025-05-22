import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat

example (h : 0 < n) : find? p (replicate n a) = if p a then some a else none := by
  unfold replicate
  unfold find?
  simp [Nat.zero_le]
  split
  · intro h1
    use a
  · intro h1
    apply Option.none_inj
  done

/- ACTUAL PROOF OF List.find?_replicate_of_length_pos -/

example (h : 0 < n) : find? p (replicate n a) = if p a then some a else none := by
  simp [find?_replicate, Nat.ne_of_gt h]