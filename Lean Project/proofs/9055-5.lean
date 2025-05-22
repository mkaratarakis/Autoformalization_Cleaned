import Init.Data.Fin.Lemmas
import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Pairwise

open List


example {l : List α} {is : List (Fin l.length)} (h : is.Pairwise (·.val < ·.val)) :
    is.map (get l) <+ l := by
  induction is generalizing l
  case nil =>
    simp only [map, get]
    apply Sublist.refl
  case cons =>
    simp only [map, get]
    apply Sublist.cons
    case cons.ih =>
      apply cons.ih
      case cons.ih.ih =>
        apply cons.ih.ih

/- ACTUAL PROOF OF List.map_get_sublist -/

example {l : List α} {is : List (Fin l.length)} (h : is.Pairwise (·.val < ·.val)) :
    is.map (get l) <+ l := by
  simpa using map_getElem_sublist h