import Mathlib
open Real
open Function

-- If `h : P ∧ Q`, then `h.1 : P` and `h.2 : Q`
-- We can prove conjunctions with the `constructor` tactic
-- `rcases h with ⟨hP, hQ⟩` gives two new assumptions `hP : P` and `hQ : Q`
-- If `h : P ↔ Q`, then `rcases h with ⟨hPQ, hQP⟩` gives `hPQ : P → Q` and `hQP : Q → P`
theorem example_one_conjunction (p q r s : Prop) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by
  intro hpq
  rcases hpq with ⟨hp, hq⟩
  constructor
  · exact h hp
  · exact h' hq

theorem example_two_conjunction (p q r s : Prop) (h : p → r) (h' : q → s) : p ∧ q → r ∧ s := by
  intro hpq
  exact ⟨h hpq.1, h' hpq.2⟩

theorem example_three_conjunction (p q r : Prop) : (p → (q → r)) ↔ p ∧ q → r := by
  constructor
  · intro h h'
    rcases h' with ⟨hp, hq⟩
    exact h hp hq
  · intro h hp hq
    apply h
    constructor
    · exact hp
    · exact hq

-- The `tauto` tactic can prove true statements in propositional logic
theorem example_four_conjunction (p q r : Prop) : (p → (q → r)) ↔ p ∧ q → r := by
  tauto


-- To prove existentials like `∃ x, P x`, we give some `x₀` to prove `P x₀`
theorem example_five_existential : ∃ n : ℕ, 8 = 2 * n := by
  use 4

theorem example_six_existential (n : ℕ) (h : ∃ k : ℕ, n = k + 1) : n > 0 := by
  rcases h with ⟨k₀, hk₀⟩  -- fixing `k₀` such that `n = k₀ + 1`
  rw [hk₀]
  exact Nat.succ_pos k₀

-- `a ∣ b ↔ ∃ k, b = a * k`
theorem example_seven_existential (a b c : ℤ) (h₁ : a ∣ b) (h₂ : b ∣ c) : a ∣ c := by
  rcases h₁ with ⟨k, hk⟩
  rcases h₂ with ⟨l, hl⟩
  use k * l
  calc
    c = b * l := hl
    _ = (a * k) * l := by rw [hk]
    _ = a * (k * l) := by ring


-- `Surjective (f : X → Y) := ∀ y, ∃ x, f x = y`
theorem example_eight_existential (f g : ℝ → ℝ) (h : Surjective (g ∘ f)) : Surjective g := by
  intro y
  rcases h y with ⟨w, hw⟩
  use f w
  exact hw
