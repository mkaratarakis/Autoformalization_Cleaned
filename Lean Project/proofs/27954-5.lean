import Init.Util
import Init.GetElem




example [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    (c : cont) (i : idx) (h : dom c i) [Decidable (dom c i)] : c[i]? = some (c[i]'h) := by
  rw [if_pos (Decidable.decide_is_true (inferInstance : Decidable (dom c i)) h)]

/- ACTUAL PROOF OF getElem?_pos -/

example [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    (c : cont) (i : idx) (h : dom c i) [Decidable (dom c i)] : c[i]? = some (c[i]'h) := by
  rw [getElem?_def]
  exact dif_pos h