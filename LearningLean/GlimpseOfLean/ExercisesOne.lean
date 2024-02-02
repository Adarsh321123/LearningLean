import Mathlib
open Real

theorem example_one_ring (a b c : ℝ) : (a * b) * c = b * (a * c) := by
  ring  -- applies properties of rings


theorem example_two_ring (a b : ℝ) : (a + b) ^ 2 = a ^ 2 + 2 * a * b + b ^ 2 := by
  ring

theorem example_three_rw (a b c d e : ℝ) (h : a = b + c) (h' : b = d - e) : a + e = d + c := by
  -- rw [h] -- rewriting to replace the assumption in the theorem, this changes the current goal
  -- rw [h']
  rw [h, h'] -- simpler
  ring

theorem example_four_rw (a b c d : ℝ) (h : b = d + d) (h' : a = b + c) : a + b = c + 4 * d := by
  rw [h', h]  -- notice the order of the rewritings
  ring

theorem example_five_rw (a b c : ℝ) : exp (a + b + c) = exp a * exp b * exp c := by
  -- rw [exp_add (a + b) c]  -- exp_add lemma says exp (x + y) = exp x * exp y
  -- rw [exp_add a b]
  rw [exp_add, exp_add]  -- Lean rewrites the first matching expression, so we don't
  -- need to provide arguments




theorem example_six_rw (a b c : ℝ) : exp (a + b - c) = (exp a * exp b) / (exp c * exp 0) := by
  -- exp_sub (x - y) = exp(x) - exp(y)
  -- exp_zero : exp 0 = 1
  rw [exp_sub, exp_add, exp_zero]
  ring

theorem example_seven_rw (a b c : ℝ) (h : a = b + c) (h' : a + e = d + c) : b + c + e = d + c := by
  rw [← h, h']  -- ← replaces right side of equality with left side

theorem example_eight_rw (a b c d : ℝ) (h : a = b + b) (h' : b = c) (h'' : a = d) : b + c = d := by
  rw [← h'', h, h']

theorem example_nine_rw (a b c d : ℝ) (h : c = d * a - b) (h' : b = a * d) : c = 0 := by
  -- you could rewrite as usual
  -- or, you can write in the assumption itself
  rw [h'] at h
  rw [h]
  ring

theorem example_nine_calc_rw (a b c d : ℝ) (h : c = b * a - d) (h' : d = a * b) : c = 0 := by
  calc  -- we can give a more natural layout by showing steps like we do on paper
    c = b * a - d := by rw[h]
    _ = b * a - a * b := by rw[h']
    _ = 0 := by ring

theorem example_ten_rw (a b c d : ℝ) (h : c = d * a + b) (h' : b = a * d) : c = 2 * a * d := by
  rw [h, h']
  ring
