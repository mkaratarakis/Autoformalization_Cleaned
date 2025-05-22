import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat

example {f : α → β → γ} {i : Nat} :
    (List.zipWith f as bs)[i]? = match as[i]?, bs[i]? with
      | some a, some b => some (f a b) | _, _ => none := by
  induction as generalizing bs i
  case nil =>
    cases bs
    case nil =>
      simp
      rfl
    case cons =>
      simp
      rfl
  case cons =>
    induction bs generalizing i
    case nil =>
      simp
      rfl
    case cons =>
      cases i
      case zero =>
        simp
        rfl
      case succ =>
        simp
        have ih :
          (zipWith f as_tl bs_tl)[i]? = match as_tl[i]?, bs_tl[i]? with
          | some a, some b => some (f a b) | _, _ => none :=
          zipWith_nth_le_aux as_ih bs_tl
        rw [ih]
        simp
        apply ih

/- ACTUAL PROOF OF List.getElem?_zipWith -/

example {f : α → β → γ} {i : Nat} :
    (List.zipWith f as bs)[i]? = match as[i]?, bs[i]? with
      | some a, some b => some (f a b) | _, _ => none := by
  induction as generalizing bs i with
  | nil => cases bs with
    | nil => simp
    | cons b bs => simp
  | cons a as aih => cases bs with
    | nil => simp
    | cons b bs => cases i <;> simp_all