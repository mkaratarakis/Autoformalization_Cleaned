import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option


example (f : α → β) (x : α) (o : Option α) :
  (o.map f).getD (f x) = f (getD o x) := by
  cases o
  · simp [map, getD]
    rfl
  · simp [map, getD]

/- ACTUAL PROOF OF Option.getD_map -/

example (f : α → β) (x : α) (o : Option α) :
  (o.map f).getD (f x) = f (getD o x) := by
  cases o <;> rfl