import Init.Prelude
import Init.SizeOf
import Init.Core

open Thunk



example [SizeOf α] (a : Thunk α) : sizeOf a = 1 + sizeOf a.get := by
   cases a; rfl