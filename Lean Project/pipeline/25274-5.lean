import Init.BinderPredicates
example
example : {b : Bool} → b = false ↔ b ≠ true := by
  constructor
  · intro h
    exact Ne.symm (Ne.ofEqFun h)
  · intro h
    exact Eq.symm (Eq.ofNeFun h)

/- ACTUAL PROOF OF Bool.eq_false_iff -/

example : {b : Bool} → b = false ↔ b ≠ true := by
  decide