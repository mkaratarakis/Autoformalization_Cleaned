import Init.Data.List.Lemmas
import Init.Data.List.TakeDrop

open List
open Nat


example {l : List α} (h : l.length ≤ i) : take i l = l := by
  have := take_append_drop i l
  rw [drop_of_length_le h, append_nil] at this; exact this