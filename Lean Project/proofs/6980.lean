import Init.Data.Array.Lemmas
import Init.Data.List.Impl

open List


example : @unzip = @unzipTR := by
  funext α β
  funext l
  induction l with
  | nil =>
    show unzip [] = unzipTR []
    rfl
  | cons hd tl ih =>
    show unzip ((hd.1, hd.2) :: tl) = unzipTR ((hd.1, hd.2) :: tl)
    simp only [unzip, unzipTR, ih]
    rfl

/- ACTUAL PROOF OF List.unzip_eq_unzipTR -/

example : @unzip = @unzipTR := by
  funext α β l; simp [unzipTR]; induction l <;> simp [*]