import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat


example : (unzip l).fst = l.map Prod.fst := by
  induction l <;> simp_all