import Init.Util
import Init.GetElem

open Fin



example [h : GetElem? Cont Nat Elem Dom] (a : Cont) (i : Fin n) : a[i]? = a[i.1]? := by
  rfl