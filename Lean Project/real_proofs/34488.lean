import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat


example (p : α → Bool) :
    (replicate n a).takeWhile p = (replicate n a).filter p := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [replicate_succ, takeWhile_cons]
    split <;> simp_all