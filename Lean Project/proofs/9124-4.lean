import Init.Data.Fin.Lemmas
import Init.Data.List.Nat.TakeDrop
import Init.Data.List.Pairwise
import Init.Data.List.Nat.Pairwise

open List


example {l : List α} {is : List (Fin l.length)} (h : is.Pairwise (· < ·)) :
    is.map (l[·]) <+ l := by
  induction is with
  | nil =>
    simp
    apply Sublist.refl
  | cons hd tl ih =>
    simp
    apply Sublist.cons
    . simp
      exact l.nthLe hd
    . apply ih
      apply Pairwise.tail h
    . simp
      apply drop_sublist_drop
      simp
      exact Fin.le_val hd

/- ACTUAL PROOF OF List.map_getElem_sublist -/

example {l : List α} {is : List (Fin l.length)} (h : is.Pairwise (· < ·)) :
    is.map (l[·]) <+ l := by
  suffices ∀ n l', l' = l.drop n → (∀ i ∈ is, n ≤ i) → map (l[·]) is <+ l'
    from this 0 l (by simp) (by simp)
  rintro n l' rfl his
  induction is generalizing n with
  | nil => simp
  | cons hd tl IH =>
    simp only [Fin.getElem_fin, map_cons]
    have := IH h.of_cons (hd+1) (pairwise_cons.mp h).1
    specialize his hd (.head _)
    have := (drop_eq_getElem_cons ..).symm ▸ this.cons₂ (get l hd)
    have := Sublist.append (nil_sublist (take hd l |>.drop n)) this
    rwa [nil_append, ← (drop_append_of_le_length ?_), take_append_drop] at this
    simp [Nat.min_eq_left (Nat.le_of_lt hd.isLt), his]