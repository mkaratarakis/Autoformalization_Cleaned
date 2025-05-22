import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option


example {o : Option α} {f : α → Option β} :
    o.bind f = none ↔ ∀ b a, a ∈ o → b ∉ f a := by
rw [bind, Option.mem_def, Option.not_mem_def, Option.bind_def]
apply Iff.intro
. intro h b a a_in_o
  rw [Option.mem_def, Option.not_mem_def] at a_in_o
  cases a_in_o
  . exfalso
    apply h
    exists a
  . apply Option.not_mem_none
. intro h
  by_cases h_o : o = none
  . rw [h_o, none_bind]
  . rw [Option.mem_def, Option.not_mem_def] at h_o
    cases h_o
    exists a
    apply h
    exists a
    rw [Option.mem_def, Option.not_mem_def]
    exists b
    apply Option.mem_some

/- ACTUAL PROOF OF Option.bind_eq_none' -/

example {o : Option α} {f : α → Option β} :
    o.bind f = none ↔ ∀ b a, a ∈ o → b ∉ f a := by
  simp only [eq_none_iff_forall_not_mem, not_exists, not_and, mem_def, bind_eq_some]