import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example {p q : Prop} (hp : p) (hq : q) : HEq hp hq := by
  have hpq : p ↔ q
  exact ⟨(fun h => True.intro), (fun h => True.intro)⟩
  convert HEq.refl hpq.mp hp
  apply hpq.mpr
  exact hq

/- ACTUAL PROOF OF proof_irrel_heq -/

example {p q : Prop} (hp : p) (hq : q) : HEq hp hq := by
  cases propext (iff_of_true hp hq); rfl