import Init.Data.List.Lemmas
import Init.Data.List.Find

open List
open Nat

example (l) (h : (f a).isSome) : findSome? f (a :: l) = f a := by
  dsimp [findSome?]
  cases h' : f a
  · exfalso
    exact h (Option.isSome_iff_ne_none.mpr h')
  · rfl

/- ACTUAL PROOF OF List.findSome?_cons_of_isSome -/

example (l) (h : (f a).isSome) : findSome? f (a :: l) = f a := by
  simp only [findSome?]
  split <;> simp_all