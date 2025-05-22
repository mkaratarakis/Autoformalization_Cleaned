import Init.Data.ByteArray
import Init.Data.String.Extra

open String



example (s : String) : s.toUTF8.size = s.utf8ByteSize := by
  simp [toUTF8, ByteArray.size, Array.size, utf8ByteSize, List.bind]
  induction s.data <;> simp [List.map, List.join, utf8ByteSize.go, Nat.add_comm, *]