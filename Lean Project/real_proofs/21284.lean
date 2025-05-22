import Init.Data.Array.Lemmas
import Init.Data.List.Impl

open List



example : @intersperse = @intersperseTR := by
  funext α sep l; simp [intersperseTR]
  match l with
  | [] | [_] => rfl
  | x::y::xs => simp [intersperse]; induction xs generalizing y <;> simp [*]