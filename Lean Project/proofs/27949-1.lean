import Init.Util
import Init.GetElem




example [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    (c : cont) (i : idx) (h : ¬dom c i) [Decidable (dom c i)] : c[i]? = none := by
  unfold getElem?
  split
  · exfalso
    exact h
  · rfl

/- ACTUAL PROOF OF getElem?_neg -/

example [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    (c : cont) (i : idx) (h : ¬dom c i) [Decidable (dom c i)] : c[i]? = none := by
  rw [getElem?_def]
  exact dif_neg h