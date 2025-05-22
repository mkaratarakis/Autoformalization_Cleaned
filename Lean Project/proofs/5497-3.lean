import Init.Core
import Init.NotationExtra
import Init.PropLemmas




example [h : Decidable p] :
    ite p False q ↔ ¬p ∧ q := by
  cases h with
  | isTrue hp =>
    simp [hp]
    exact Iff.intro (fun hn => False.elim (hn hp)) (fun hn => hn.elim)
  | isFalse hn =>
    simp [hn]
    exact Iff.intro (fun h => And.intro hn h) (fun h => h.right)

/- ACTUAL PROOF OF if_false_left -/

example [h : Decidable p] :
    ite p False q ↔ ¬p ∧ q := by
  cases h <;> (rename_i g; simp [g])