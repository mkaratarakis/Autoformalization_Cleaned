import Init.Data.List.TakeDrop
import Init.Data.List.Zip

open List
open Nat


example : (zipWith f l l').tail = zipWith f l.tail l'.tail := by
  rw [← drop_one]; simp [drop_zipWith]