import Init.Data.Option.BasicAux
import Init.Data.Option.Instances
import Init.Classical
import Init.Ext
import Init.Data.Option.Lemmas

open Option


example {f : α → β → Option γ} (a : Option α) (b : Option β) :
    (a.bind fun x => b.bind (f x)) = b.bind fun y => a.bind fun x => f x y := by
  cases a <;> cases b <;> rfl

/- ACTUAL PROOF OF Option.bind_comm -/

example {f : α → β → Option γ} (a : Option α) (b : Option β) :
    (a.bind fun x => b.bind (f x)) = b.bind fun y => a.bind fun x => f x y := by
  cases a <;> cases b <;> rfl