import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option


example {o : Option α} {f : α → Option β} :
    o.bind f = none ↔ ∀ a, o = some a → f a = none := by
  cases o <;> simp only [bind_eq_none, bind_none]
  · exact ⟨fun h a h', h h', fun h', h' (Option.get _ _) rfl⟩
  · exact ⟨fun h a h', h, fun h, h⟩

/- ACTUAL PROOF OF Option.bind_eq_none -/

example {o : Option α} {f : α → Option β} :
    o.bind f = none ↔ ∀ a, o = some a → f a = none := by
  cases o <;> simp