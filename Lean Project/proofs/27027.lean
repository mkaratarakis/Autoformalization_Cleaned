import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat

example {a : α} {b : β} {n : Nat} :
    zipWithAll f (replicate n a) (replicate n b) = replicate n (f a b) := by
  induction n with
  | zero =>
    simp [replicate, zipWithAll]
  | succ k ih =>
    simp [replicate, zipWithAll, ih]

/- ACTUAL PROOF OF List.zipWithAll_replicate -/

example {a : α} {b : β} {n : Nat} :
    zipWithAll f (replicate n a) (replicate n b) = replicate n (f a b) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [replicate_succ, ih]