import Mathlib
open Real

theorem level_one (x q : ℕ) : 37 * x + q = 37 * x + q := by
  rfl  -- proves theorems of the form X = X

theorem level_two (x y : ℕ) (h : y = x + 7) : 2 * y = 2 * (x + 7) := by
  rw [h]  -- Lean thinks h is a secret proof of the assumption, so we
  -- replace y with x + 7
