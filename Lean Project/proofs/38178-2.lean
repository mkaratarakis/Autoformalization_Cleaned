import Init.Data.List.Basic
import Init.Data.Char.Basic
import Init.Data.Option.Basic
import Init.Data.String.Basic

open String


example (s : String) (i : Pos) (h : i ≠ 0) : (s.prev i).1 < i.1 := by
  rw [prev]
  simp [h]

  have h' : 0 < i := by
    simpa using h

  have h'' : s.toList.length ≥ i := by
    simpa using i.2

  apply utf8PrevAux_lt
  assumption

/- ACTUAL PROOF OF String.prev_lt_of_pos -/

example (s : String) (i : Pos) (h : i ≠ 0) : (s.prev i).1 < i.1 := by
  simp [prev, h]
  exact utf8PrevAux_lt_of_pos _ _ _ h