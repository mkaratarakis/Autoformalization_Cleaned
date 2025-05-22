import Init.Data.ByteArray
import Init.Data.String.Extra

open String


example (s : String) : s.toUTF8.size = s.utf8ByteSize := by
  rw [toUTF8, ByteArray.size, Array.size, utf8ByteSize, List.bind]
  simp
  induction s.data
  . case nil =>
    simp
  . case cons head tail ih =>
    simp [List.map, List.join, utf8ByteSize.go]
    rw [ih]
    simp [utf8ByteSize.go]

/- ACTUAL PROOF OF String.size_toUTF8 -/

example (s : String) : s.toUTF8.size = s.utf8ByteSize := by
  simp [toUTF8, ByteArray.size, Array.size, utf8ByteSize, List.bind]
  induction s.data <;> simp [List.map, List.join, utf8ByteSize.go, Nat.add_comm, *]