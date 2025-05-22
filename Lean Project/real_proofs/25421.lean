import Init.Data.List.TakeDrop
import Init.Data.List.Monadic

open List
open Nat


example [Monad m] [LawfulMonad m] (f : α → m β) :
    (a :: l).mapM f = (return (← f a) :: (← l.mapM f)) := by
  simp [← mapM'_eq_mapM, mapM']