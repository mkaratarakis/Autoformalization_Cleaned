import Init.Data.Array.Lemmas
import Init.Data.List.Impl

open List



example : @unzip = @unzipTR := by
  funext α β l; simp [unzipTR]; induction l <;> simp [*]