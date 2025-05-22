API ERROR: API error occurred: Status 429
{"message":"Requests rate limit exceeded"}

/- ACTUAL PROOF OF BitVec.ushiftRightRec_succ -/

example (x : BitVec w₁) (y : BitVec w₂) :
    ushiftRightRec x y (n + 1) = (ushiftRightRec x y n) >>> (y &&& twoPow w₂ (n + 1)) := by
  simp [ushiftRightRec]