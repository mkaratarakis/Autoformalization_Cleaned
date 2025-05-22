import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat

example : (unzip l).fst = l.map Prod.fst := by
  induction l with
  | nil =>
    simp [unzip, map]
  | cons hd tl ih =>
    simp [unzip, map, ih]

/- ACTUAL PROOF OF List.unzip_fst -/

example : (unzip l).fst = l.map Prod.fst := by
  induction l <;> simp_all