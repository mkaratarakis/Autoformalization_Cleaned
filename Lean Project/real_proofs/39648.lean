import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat


example (h : ¬ p a) : find? p (replicate n a) = none := by
  simp [find?_replicate, h]