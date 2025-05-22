import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat


example : (zipWith f l l').drop n = zipWith f (l.drop n) (l'.drop n) := by
  induction l generalizing l' n with
  | nil => simp
  | cons hd tl hl =>
    · cases l'
      · simp
      · cases n
        · simp
        · simp [hl]