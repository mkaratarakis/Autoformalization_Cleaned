import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat

example {a : α} {b : β} {n : Nat} :
    zip (replicate n a) (replicate n b) = replicate n (a, b) := by
  induction n with
  | zero =>
    simp [replicate, zip]
  | succ k hk =>
    have h1 : replicate k a = replicate (Nat.pred (k + 1)) a := by
      simp [Nat.pred]
    have h2 : replicate k b = replicate (Nat.pred (k + 1)) b := by
      simp [Nat.pred]
    have h3 : replicate (k + 1) a = a :: replicate k a := by
      simp [replicate]
    have h4 : replicate (k + 1) b = b :: replicate k b := by
      simp [replicate]
    simp [zip, h3, h4]
    rw [hk]
    simp [zip, replicate]

/- ACTUAL PROOF OF List.zip_replicate' -/

example {a : α} {b : β} {n : Nat} :
    zip (replicate n a) (replicate n b) = replicate n (a, b) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [replicate_succ, ih]