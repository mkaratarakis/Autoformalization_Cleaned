import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option


example (f : α → β) (g : β → γ) :
    Option.map g ∘ Option.map f = Option.map (g ∘ f) := by
  funext x
  cases x
  · simp [map]
  · simp [map, Function.comp]

/- ACTUAL PROOF OF Option.map_comp_map -/

example (f : α → β) (g : β → γ) :
    Option.map g ∘ Option.map f = Option.map (g ∘ f) := by
  funext x; simp