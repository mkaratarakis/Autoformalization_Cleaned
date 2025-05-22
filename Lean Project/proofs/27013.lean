import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat

example : (unzip l).snd = l.map Prod.snd := by
  induction l
  case nil =>
    simp
  case cons =>
    simp
    rw [ih]

/- ACTUAL PROOF OF List.unzip_snd -/

example : (unzip l).snd = l.map Prod.snd := by
  induction l <;> simp_all