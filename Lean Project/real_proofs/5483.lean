import Init.Core
import Init.NotationExtra
import Init.PropLemmas





example {p q : Prop} (hp : p) (hq : q) : HEq hp hq := by
  cases propext (iff_of_true hp hq); rfl