import Init.Data.List.TakeDrop
import Init.Data.List.Sublist

open List
open Nat
variable [BEq α]


example {L : List α} (h : 0 < L.length) : isPrefixOf L [] = false := by
  cases L <;> simp_all [isPrefixOf]