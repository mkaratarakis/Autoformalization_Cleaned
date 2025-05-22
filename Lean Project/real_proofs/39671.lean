import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat


example (_ : (f a).isSome) : findSome? f (replicate n a) = if n = 0 then none else f a := by
  simp [findSome?_replicate]