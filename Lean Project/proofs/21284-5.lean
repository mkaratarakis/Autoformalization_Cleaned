import Init.Data.Array.Lemmas
import Init.Data.List.Impl

open List


example : @intersperse = @intersperseTR := by
  funext α sep l
  induction' l with x xs ih
  · simp [intersperse, intersperseTR]
  · cases xs
    · simp [intersperse, intersperseTR]
    · simp [intersperse, intersperseTR]
      rw [ih]

/- ACTUAL PROOF OF List.intersperse_eq_intersperseTR -/

example : @intersperse = @intersperseTR := by
  funext α sep l; simp [intersperseTR]
  match l with
  | [] | [_] => rfl
  | x::y::xs => simp [intersperse]; induction xs generalizing y <;> simp [*]