import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option



example {x : Option α} (h : ∀ a, a ∈ x → f a = g a) : x.map f = x.map g := by
  cases x <;> simp only [map_none', map_some', h, mem_def]