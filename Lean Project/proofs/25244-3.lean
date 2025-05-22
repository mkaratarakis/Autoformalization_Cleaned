import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option

example {α α₁ : Type} {x : Option α} (f g : α → α₁) (h : ∀ a, a ∈ x → f a = g a) : x.map f = x.map g := by
  cases x with
  | none =>
    rfl
  | some a =>
    have : f a = g a := h a (Option.mem_some.2 rfl)
    rw[this]

/- ACTUAL PROOF OF Option.map_congr -/

example {x : Option α} (h : ∀ a, a ∈ x → f a = g a) : x.map f = x.map g := by
  cases x <;> simp only [map_none', map_some', h, mem_def]