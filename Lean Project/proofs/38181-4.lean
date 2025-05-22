import Init.Data.List.Basic
import Init.Data.Char.Basic
import Init.Data.Option.Basic
import Init.Data.String.Basic

open String


example (c : Char) (n : Nat) : (pushn s c n).length = s.length + n := by
  induction n with
  | zero =>
    rfl
  | succ k ih =>
    simp [pushn]
    rw [ih, String.length_push]
    rfl

/- ACTUAL PROOF OF String.length_pushn -/

example (c : Char) (n : Nat) : (pushn s c n).length = s.length + n := by
  unfold pushn; induction n <;> simp [Nat.repeat, Nat.add_assoc, *]