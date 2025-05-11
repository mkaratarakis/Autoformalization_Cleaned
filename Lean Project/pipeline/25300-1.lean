import Init.BinderPredicates
example (a ↔ b) := by
begin
  cases b with
  | false =>
    simp
    cases a with
    | false =>
      simp
    | true =>
      simp
  | true =>
    simp
    cases a with
    | false =>
      simp
    | true =>
      simp
end

/- ACTUAL PROOF OF Bool.eq_iff_iff -/

example {a b : Bool} : a = b ↔ (a ↔ b) := by
  cases b <;> simp