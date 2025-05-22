import Init.Control.Basic
import Init.Data.List.Basic
import Init.Data.List.Control

open List



example [Monad m] (f : β → α → m β) (b) (a) (l : List α) :
    (a :: l).foldlM f b = f b a >>= l.foldlM f := by
  simp [List.foldlM]