import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat


example : (unzip l).snd = l.map Prod.snd := by
  induction l <;> simp_all