import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example {p q : Prop} (hp : p) (hq : q) : HEq hp hq := by
  have hpq : p ↔ q := by
    constructor
    · intro hp'
      exact hq
    · intro hq'
      exact hp
  apply HEq.symm
  apply HEq.refl hq

/- ACTUAL PROOF OF proof_irrel_heq -/

example {p q : Prop} (hp : p) (hq : q) : HEq hp hq := by
  cases propext (iff_of_true hp hq); rfl