import Init.Util
import Init.GetElem




example [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    (c : cont) (i : idx) (h : dom c i) [Decidable (dom c i)] : c[i]? = some (c[i]'h) := by
  rw [show c[i]? = some (c[i]'h) from if_pos h]

/- ACTUAL PROOF OF getElem?_pos -/

example [GetElem? cont idx elem dom] [LawfulGetElem cont idx elem dom]
    (c : cont) (i : idx) (h : dom c i) [Decidable (dom c i)] : c[i]? = some (c[i]'h) := by
  rw [getElem?_def]
  exact dif_pos h