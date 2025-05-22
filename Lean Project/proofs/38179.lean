import Init.Data.List.Basic
import Init.Data.Char.Basic
import Init.Data.Option.Basic
import Init.Data.String.Basic

open String


example (c : Char) : (String.push s c).length = s.length + 1 := by
  simp [String.push, String.length]
  simp [List.length]
  rw [Nat.succ]

/- ACTUAL PROOF OF String.length_push -/

example (c : Char) : (String.push s c).length = s.length + 1 := by
  rw [push, length_mk, List.length_append, List.length_singleton, Nat.succ.injEq]
  rfl