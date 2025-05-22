import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat

example {l : List α} (p : α → Bool) n :
    (l.takeWhile p).take n = (l.take n).takeWhile p := by
  induction l with
  | nil =>
    simp
  | cons x xs ih =>
    cases hp : p x
    · cases n with
      | zero =>
        simp
      | succ n =>
        simp [takeWhile, take]
        exact takeWhile_eq_nil.2 hp
    · cases n with
      | zero =>
        simp
      | succ n =>
        simp [takeWhile, take]
        rw [ih]
        rfl

/- ACTUAL PROOF OF List.take_takeWhile -/

example {l : List α} (p : α → Bool) n :
    (l.takeWhile p).take n = (l.take n).takeWhile p := by
  induction l generalizing n with
  | nil => simp
  | cons x xs ih =>
    by_cases h : p x <;> cases n <;> simp [takeWhile_cons, h, ih, take_succ_cons]