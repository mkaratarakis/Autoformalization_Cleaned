import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat


example (h : (f a).isNone) : findSome? f (replicate n a) = none := by
  rw [Option.isNone_iff_eq_none] at h
  simp [findSome?_replicate, h]