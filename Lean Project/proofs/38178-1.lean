import Init.Data.List.Basic
import Init.Data.Char.Basic
import Init.Data.Option.Basic
import Init.Data.String.Basic

open String


example (s : String) (i : Pos) (h : i ≠ 0) : (s.prev i).1 < i.1 := by
  rw [prev]
  rw [Option.getD _ h]
  apply utf8PrevAux_lt

def prev (i : Pos) : Option Pos :=
  Option.guard (i ≠ 0) <| utf8PrevAux s.data 0 i
example :
    ∀ (cs : List Char) (i p : Pos), p ≠ 0 → (utf8PrevAux cs i p).1 < p.1
  | _, _, _, h => _

/- ACTUAL PROOF OF String.prev_lt_of_pos -/

example (s : String) (i : Pos) (h : i ≠ 0) : (s.prev i).1 < i.1 := by
  simp [prev, h]
  exact utf8PrevAux_lt_of_pos _ _ _ h