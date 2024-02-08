import Mathlib
open Real

/-
If `P` is a predicate of type `X`, then for every object `x` with type `X`, then we get a statement `P x` (type `Prop`).
If we have a proof `h` of `∀ x, P x`, then Lean sees it as a function sending any `x : X` to a proof `h x` of `P x`.
We use `intro` to fix an arbitrary object of type `X`.
If the type of `P` is clear, Lean can infer the type of `x`.
-/

-- let's define a predicate
def even_fun (f : ℝ → ℝ) := ∀ x, f (-x) = f x

-- `unfold` unfolds definitions (note that we actually didn't need to use it here
-- since `unfold`, `apply`, `exact`, `rfl`, and `calc` among others auto unfold definitions,
-- but tactics like `rw`, `ring`, and `linarith` will not unfold definitions in the goal)
-- `rfl` proves equalities that are reflexive
theorem example_one_for_all (f g : ℝ → ℝ) (hf : even_fun f) (hg : even_fun g) : even_fun (f + g) := by
  unfold even_fun at hf
  unfold even_fun at hg
  unfold even_fun
  intro x
  calc
    (f + g) (-x) = f (-x) + g (-x) := by rfl
    _ = f x + g (-x) := by rw [hf x]  -- actually, we don't need to tell Lean that hf should be specialized to x
    _ = f x + g x := by rw [hg x]
    _ = (f + g) x := by rfl  -- not necessary since only proves something is true
    -- by definition, and it is not followed by rw

-- compressed version
theorem example_two_for_all (f g : ℝ → ℝ) : even_fun f → even_fun g → even_fun (f + g) := by
  intro hf hg x
  calc
    (f + g) (-x) = f (-x) + g (-x) := by rfl
    _ = f x + g x := by rw [hf, hg]

theorem example_three_for_all (f g : ℝ → ℝ) (hf : even_fun f) : even_fun (g ∘ f) := by
  intro x
  calc
    (g ∘ f) (-x) = g (f (-x)) := by rfl
    _ = g (f x) := by rw [hf]

def non_decreasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≤ f x₂

def non_increasing (f : ℝ → ℝ) := ∀ x₁ x₂, x₁ ≤ x₂ → f x₁ ≥ f x₂

-- using forward reasoning
theorem example_four_for_all (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by
  -- let `x₁` and `x₂` be real numbers such that `x₁ ≤ x₂`
  intro x₁ x₂ h
  have step₁ : f x₁ ≤ f x₂
  · exact hf x₁ x₂ h  -- can also use `hf _ _ h` since `x₁` and `x₂` are inferred from the type of `hf`
  -- since `g` is non-decreasing, we then get `g (f x₁) ≤ g (f x₂)`
  exact hg (f x₁) (f x₂) step₁

-- can use the `specialize` tactic to replace `hf` by its specialization to the relevant value
theorem example_five_for_all (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by
  intro x₁ x₂ h
  specialize hf x₁ x₂ h
  exact hg (f x₁) (f x₂) hf

-- `specialize` is useful for exploration, or for preparing to rewrite with the assumption
-- we can also remove it and instead use an expression that involves the original assumption
theorem example_six_for_all (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by
  intro x₁ x₂ h
  exact hg (f x₁) (f x₂) (hf x₁ x₂ h)

-- using backwards reasoning
-- Lean specializes assumptions for us using "unification"
theorem example_seven_for_all (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_decreasing g) :
    non_decreasing (g ∘ f) := by
  intro x₁ x₂ h
  apply hg
  apply hf
  exact h

-- using both forwards and backwards reasoning
theorem example_eight_for_all (f g : ℝ → ℝ) (hf : non_decreasing f) (hg : non_increasing g) :
    non_increasing (g ∘ f) := by
  intro x₁ x₂ h
  apply hg
  exact hf x₁ x₂ h

-- `simp` simplifies complicated expressions
-- `apply?` will find lemmas from Lean's math library
-- `X : Set ℝ` means that `X` is a set containing only real numbers
theorem example_nine_finding_lemmas (x : ℝ) (X Y : Set ℝ) (hx : x ∈ X) : x ∈ (X ∩ Y) ∪ (X \ Y) := by
  simp
  exact hx

-- `apply?` will find the lemma that every continuous function with compact support has a global min
theorem example_ten_finding_lemmas (f : ℝ → ℝ) (hf : Continuous f) (h2f : HasCompactSupport f) : ∃ x, ∀ y, f x ≤ f y := by
  exact Continuous.exists_forall_le_of_hasCompactSupport hf h2f
