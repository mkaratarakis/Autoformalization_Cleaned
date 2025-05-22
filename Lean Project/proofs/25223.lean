import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option


example (h : β → γ) (g : α → β) (x : Option α) :
    (x.map g).map h = x.map (h ∘ g) := by
  cases x
  · simp
  · simp

/- ACTUAL PROOF OF Option.map_map -/

example (h : β → γ) (g : α → β) (x : Option α) :
    (x.map g).map h = x.map (h ∘ g) := by
  cases x <;> simp only [map_none', map_some', ·∘·]