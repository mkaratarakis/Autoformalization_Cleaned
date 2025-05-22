API ERROR: API error occurred: Status 400
{"object":"error","message":"Assistant message must have either content or tool_calls, but not none.","type":"invalid_request_error","param":null,"code":null}

/- ACTUAL PROOF OF List.takeWhile_cons_of_neg -/

example {p : α → Bool} {a : α} {l : List α} (h : ¬ p a) :
    (a :: l).takeWhile p = [] := by
  simp [takeWhile_cons, h]