import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat

example : (zipWith f l l').take n = zipWith f (l.take n) (l'.take n) := by
  induction l generalizing l' with
  | nil =>
    simp [zipWith, take]
  | cons hd tl ih =>
    cases l' with
    | nil =>
      simp [zipWith, take]
    | cons head tail =>
      cases n with
      | zero =>
        simp [take]
      | succ n' =>
        simp [take, zipWith]
        apply ih

/- ACTUAL PROOF OF List.take_zipWith -/

example : (zipWith f l l').take n = zipWith f (l.take n) (l'.take n) := by
  induction l generalizing l' n with
  | nil => simp
  | cons hd tl hl =>
    cases l'
    · simp
    · cases n
      · simp
      · simp [hl]