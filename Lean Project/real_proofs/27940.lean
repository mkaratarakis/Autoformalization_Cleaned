import Init.Util
import Init.GetElem





example [GetElem coll idx elem valid] {c d : coll} {i : idx} {h : valid c i}
    (h' : c = d) : c[i] = d[i]'(h' ▸ h) := by
  cases h'; rfl