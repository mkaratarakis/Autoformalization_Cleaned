import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat


example (p : α → Bool) :
    (replicate n a).dropWhile p = (replicate n a).filter (fun a => !p a) := by
  induction n with
  | zero => simp
  | succ n ih =>
    simp only [replicate_succ, dropWhile_cons]
    split <;> simp_all