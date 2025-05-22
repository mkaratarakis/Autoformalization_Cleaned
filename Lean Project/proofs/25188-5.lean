import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option


example {o : Option α} {f : α → Option β} :
    o.bind f = none ↔ ∀ b a, a ∈ o → b ∉ f a := by
  constructor
  · intro h1 b a ha
    have h2 : o.bind f = none := h1
    cases o <;> simp [bind] at h2
    · exfalso
      apply ha
      contradiction
    · exfalso
      apply ha
      contradiction
  · intro h1
    by_cases h : o = none
    · simp [h]
    · simp [h]
      cases h : o <;> simp [bind, h]
      intro b a ha
      exact h1 b a (Or.inr rfl)

/- ACTUAL PROOF OF Option.bind_eq_none' -/

example {o : Option α} {f : α → Option β} :
    o.bind f = none ↔ ∀ b a, a ∈ o → b ∉ f a := by
  simp only [eq_none_iff_forall_not_mem, not_exists, not_and, mem_def, bind_eq_some]