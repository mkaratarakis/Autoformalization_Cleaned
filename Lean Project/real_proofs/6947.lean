import Init.Data.Array.Lemmas
import Init.Data.List.Impl

open List



example (f : α → β) (as : List α) (bs : List β) :
    mapTR.loop f as bs = bs.reverse ++ map f as := by
  induction as generalizing bs with
  | nil => simp [mapTR.loop, map]
  | cons a as ih =>
    simp only [mapTR.loop, map]
    rw [ih (f a :: bs), reverse_cons, append_assoc]
    rfl