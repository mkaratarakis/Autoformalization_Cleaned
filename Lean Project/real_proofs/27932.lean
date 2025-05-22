import Init.Util
import Init.GetElem

open List



example (a : α) (as : List α) (h : 0 < (a :: as).length) : getElem (a :: as) 0 h = a := by
  rfl