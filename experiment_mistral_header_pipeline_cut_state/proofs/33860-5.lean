import Mathlib.Algebra.Group.Defs
import Mathlib.Algebra.Group.Invertible.Defs

open Invertible
variable {α : Type*} [Monoid α]
variable {α : Type u}

example [Monoid α] (a b : α) [Invertible a] [Invertible b] (h : a = b) :
    ⅟a = ⅟b := by
  rw [h]
  exact invertible_unique _ _ _ rfl

/- ACTUAL PROOF OF Invertible.congr -/

example [Monoid α] (a b : α) [Invertible a] [Invertible b] (h : a = b) :
    ⅟a = ⅟b := by
  subst h; congr; apply Subsingleton.allEq