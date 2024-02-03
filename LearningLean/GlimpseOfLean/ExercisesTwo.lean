import Mathlib
open Real

-- Leans writes an implication as → since it sees
-- a proof of P → Q as a function that sends a proof of P to a proof of Q
-- the lemma `sq_pos_of_pos` claims `0 < a → 0 < a^2`
-- so we apply the "function" `sq_pos_of_pos` to the assumption `ha`
theorem example_one_implication (a : ℝ) (ha : 0 < a) : 0 < a^2 := by
  exact sq_pos_of_pos ha  -- assumption is exactly what we need to prove

-- we can also apply backwards reasoning
theorem example_two_implication (a : ℝ) (ha : 0 < a) : 0 < (a^2)^2 := by
  apply sq_pos_of_pos
  apply sq_pos_of_pos
  exact ha  -- this is exactly our assumption ha

theorem example_three_implication (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a^2 + b^2 := by
  apply add_pos  -- `add_pos: 0 < x → 0 < y → 0 < x + y`
  -- now we have two goals to prove
  apply sq_pos_of_pos
  exact ha
  apply sq_pos_of_pos
  exact hb

-- we can also use forward reasoning using the `have` tactic
-- to introduce a subgoal, we write `have name : subgoal`
-- to prove the subgoal, we start with a `·` and then indent
-- after we prove the subgoal, we can use it using `name`
theorem example_four_implication (a : ℝ) (ha : 0 < a) : 0 < (a^2)^2 := by
  have h2 : 0 < a^2
  · apply sq_pos_of_pos  -- we apply this to the subgoal
    exact ha
  exact sq_pos_of_pos h2  -- can get to the subgoal from the original goal

theorem example_five_implication (a b : ℝ) (ha : 0 < a) (hb : 0 < b) : 0 < a^2 + b^2 := by
  have h1 : 0 < a^2
  · exact sq_pos_of_pos ha
  have h2 : 0 < b^2
  · exact sq_pos_of_pos hb
  exact add_pos h1 h2

-- use `intro` to prove an implication
-- we essentially proved an implication in the above theorem, but the premise was already
-- introduced for us
theorem example_six_proving_implication (a : ℝ) : a > 0 → b > 0 → a + b > 0 := by
  intro ha hb
  exact add_pos ha hb

-- note that `p → q → r` means `p → (q → r)`
theorem example_seven_proving_implication (p q r : Prop) : (p → q) → (p → q → r) → p → r := by
  intro h1 h2 h3
  /-
  applying h2 creates two goals: one to prove p and another to prove q (since h2 has two assumptions)
  applying h3 solves the first goal
  -/
  apply h2 h3
  /-
  applying h1 means the goal is now to prove p
  applying h3 solves this goal
  -/
  apply h1 h3

-- `sub_nonneg : 0 ≤ y - x ↔ x ≤ y`
theorem example_eight_equivalences (a b c : ℝ) : c + a ≤ c + b ↔ a ≤ b := by
  rw [← sub_nonneg]
  have key : (c + b) - (c + a) = b - a
  · ring
  rw [key]  -- uses an equality result, not an equivalence
  -- could have also just used `ring` instead
  rw [sub_nonneg]

-- this is already in Mathlib as `add_le_add_iff_right`
-- it is a function that takes as input `c`
-- and outputs a proof of `a + c ≤ b + c ↔ a ≤ b`
theorem example_nine_equivalences (a b : ℝ) (c : ℝ) : a + c ≤ b + c ↔ a ≤ b := by
  rw [← sub_nonneg]
  ring
  rw [sub_nonneg]

theorem example_ten_equivalences (a b : ℝ) (ha : 0 ≤ a) : b ≤ a + b := by
  calc
    b = 0 + b := by ring
    _ ≤ a + b := by { rw [add_le_add_iff_right b] ; exact ha }  -- `_` means `0 + b`

-- it would be more useful to view the implication as a double equivalence
-- if `h : P ↔ Q`, then
-- `h.1 : P → Q` and `h.2 : Q → P`
theorem example_eleven_equivalences (a b : ℝ) (ha : 0 ≤ a) : b ≤ a + b := by
  calc
    b = 0 + b := by ring
    _ ≤ a + b := by exact (add_le_add_iff_right b).2 ha

-- `add_le_add_iff_left a : a + b ≤ a + c ↔ b ≤ c`
theorem example_twelve_equivalences (a b : ℝ) (hb : 0 ≤ b) : a ≤ a + b := by
  calc
    a = a + 0 := by ring
    _ ≤ a + b := by exact (add_le_add_iff_left a).2 hb

-- to prove an equivalence, we use `rw` until the goal is `P ↔ P`
-- can also prove each implication separately with the `constructor` tactic
theorem example_thirteen_proving_equivalences (a b : ℝ) : (a - b) * (a + b) = 0 ↔ a^2 = b^2 := by
  constructor
  · intro h
    calc
      a^2 = b^2 + (a-b)*(a+b) := by ring
      _ = b^2 + 0 := by rw[h]
      _ = b^2 := by ring
  · intro h
    calc
      (a - b)*(a + b) = a^2 - b^2 := by ring
      _ = b^2 - b^2 := by rw[h]
      _ = 0 := by ring

theorem example_fourteen_proving_equivalences (a b : ℝ) : a = b ↔ b - a = 0 := by
  constructor
  · intro h
    rw[h]
    ring
  · intro h
    calc
      a = b - (b - a) := by ring
      _ = b - 0 := by rw[h]
      _ = b := by ring
