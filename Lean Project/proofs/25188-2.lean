import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option


example {o : Option α} {f : α → Option β} :
    o.bind f = none ↔ ∀ b a, a ∈ o → b ∉ f a := by
  rw [bind]
  split
  · intro h b a a_in_o
    cases a_in_o
    · contradiction
    · cases h
  · intro h
    cases o
    · simp
    · intro a b
      apply h
      exact Option.some a

/- ACTUAL PROOF OF Option.bind_eq_none' -/

example {o : Option α} {f : α → Option β} :
    o.bind f = none ↔ ∀ b a, a ∈ o → b ∉ f a := by
  simp only [eq_none_iff_forall_not_mem, not_exists, not_and, mem_def, bind_eq_some]