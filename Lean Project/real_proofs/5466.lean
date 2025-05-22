import Init.Core
import Init.NotationExtra
import Init.PropLemmas





example : Eq True = id := by
  funext _; simp only [true_iff, id_def, eq_iff_iff]