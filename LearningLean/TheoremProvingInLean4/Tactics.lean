/-
Proof term: representation of a mathematical proof
Tactic: commands that describe how to build a proof. They tell Lean how to construct a proof term

We will introduce tactic-style proofs, as opposed to the term-style proofs we have seen thus far.

Pro: shorter and easier to write, use Lean's automation
Con: harder to read
-/

import Mathlib

theorem test (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro
  exact hp
  apply And.intro
  exact hq
  exact hp

theorem test_simple (p q : Prop) (hp : p) (hq : q) : p ∧ q ∧ p := by
  apply And.intro hp
  exact And.intro hq hp

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  · intro h  --  `h : p ∧ (q ∨ r)`
    -- Or.elim says we can prove `r` from `p ∨ q` by showing `r` follows from `p` and `r` follows from `q`
    apply Or.elim h.right
    · intro hq
      apply Or.inl
      apply And.intro
      · exact And.left h
      · exact hq
    · intro hr
      apply Or.inr
      apply And.intro
      · exact And.left h
      · exact hr
  · intro h
    apply Or.elim h
    · intro hpq
      apply And.intro
      · exact And.left hpq
      · apply Or.inl
        exact And.right hpq
    · intro hpr
      apply And.intro
      · exact And.left hpr
      · apply Or.inr
        exact And.right hpr

-- `assumption` looks through assumptions in the context of the current goal and applies a matching conclusion
-- can use `revert` as an inverse to `intro`
example (x y : Nat) (h : x = y) : y = x := by
  revert h
  -- goal is `x = y → y = x`
  intro h₁
  apply Eq.symm
  assumption

-- can place an arbitrary expression in the goal using `generalize`
example : 3 = 3 := by
  generalize 3 = x
  revert x
  intro y
  rfl

-- `cases` decomposes a disjunction
example (p q : Prop) : p ∨ q → q ∨ p := by
  intro h
  cases h with
  | inl hp => apply Or.inr; exact hp
  | inr hq => apply Or.inl; exact hq

-- `constructor` applies the unique constructor for a conjunction, `And.intro`

example (p q : Nat → Prop) : (∃ x, p x) → ∃ x, p x ∨ q x := by
  intro h
  cases h with
  | intro x px => constructor; apply Or.inl; exact px

-- `tac1 <;> tac2` applies `tac2` to each subgoal produced by tactic `tac1`
open Nat
example (P : Nat → Prop) (h₀ : P 0) (h₁ : ∀ n, P (succ n)) (m : Nat) : P m := by
  cases m with
  | zero => exact h₀
  | succ m' => exact h₁ m'

-- `contradiction` looks for contradictions among the hypotheses of the current goal
example (p q : Prop) : p ∧ ¬ p → q := by
  intro h
  cases h  -- left is `p` and right is `¬ p`
  contradiction

example (p q r : Prop) : p ∧ (q ∨ r) ↔ (p ∧ q) ∨ (p ∧ r) := by
  apply Iff.intro
  . intro
    | ⟨hp, Or.inl hq⟩ => apply Or.inl; constructor <;> assumption
    | ⟨hp, Or.inr hr⟩ => apply Or.inr; constructor <;> assumption
  . intro
    | Or.inl ⟨hp, hq⟩ => constructor; assumption; apply Or.inl; assumption
    | Or.inr ⟨hp, hr⟩ => constructor; assumption; apply Or.inr; assumption


-- Structuring Tactic Proofs
-- can mix term and tactic proofs
-- `apply` and `exact` expect arbitrary terms, which you can write using `have` and `show`
-- when writing a term, you can invoke tactic mode by inserting a `by` block

example (p q r : Prop) : p ∧ (q ∨ r) → (p ∧ q) ∨ (p ∧ r) := by
  intro h
  exact
    have hp : p := h.left
    have hqr : q ∨ r := h.right
    show (p ∧ q) ∨ (p ∧ r) by
      cases hqr with
      | inl hq => exact Or.inl ⟨hp, hq⟩
      | inr hr => exact Or.inr ⟨hp, hr⟩

-- `show` proof term exists
-- there is also a `show` tactic which describes the goal that is about to be solved
-- it can also rewrite the goal

example (n : Nat) : n + 1 = Nat.succ n := by
  show Nat.succ n = Nat.succ n
  rfl

example : ∃ x, x + 2 = 8 := by
  let a : Nat := 6
  exists a


-- Tactic Combinators
-- form new tactics from old ones
example (p q : Prop) (hp : p) : p ∨ q :=
  by apply Or.inl; assumption  -- equivalent to a single tactic which does `apply` and then `assumption`

example (p q : Prop) (hp : p) (hq : q) : p ∧ q := by
  constructor <;> assumption

-- `try` builds tactic that always succeeds: `try t` executes `t` and reports success, even if `t` fails
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor <;> (try constructor) <;> assumption

-- `all_goals t` applies `t` to all open goals
example (p q r : Prop) (hp : p) (hq : q) (hr : r) : p ∧ q ∧ r := by
  constructor
  all_goals (try constructor)
  all_goals assumption

-- `any_goals` succeeds if its argument succeeds on at least one goal


-- Rewriting
-- we rewrite the goal using a hypothesis
example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  rw [h₂] -- replace k with 0
  rw [h₁] -- replace f 0 with 0 (automatically closes goals of the form `t = t`)


-- Simplifier
-- `simp` tactic iteratively rewrites subterms in an expression
example (x y z : Nat) : (x + 0) * (0 + y * 1 + z * 0) = x * y := by
  simp

example (x y z : Nat) (p : Nat → Prop) (h : p (x * y)) : p ((x + 0) * (0 + y * 1 + z * 0)) := by
  simp; assumption

-- you can also send `simp` a list of facts, lemmas, etc. to use
def f (m n : Nat) : Nat :=
  m + n + m

example {m n : Nat} (h : n = 1) (h' : 0 = m) : (f m n) = n := by
  simp [h, ←h', f]

-- common to simplify a goal using local hypotheses
example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [h₁, h₂]

example (f : Nat → Nat) (k : Nat) (h₁ : f 0 = 0) (h₂ : k = 0) : f k = 0 := by
  simp [*]  -- uses all hypotheses when simplifying

example (u w x x' y y' z : Nat) (p : Nat → Prop)
        (h₁ : x + 0 = x') (h₂ : y + 0 = y')
        : x + y + 0 = x' + y' := by
  simp at *  -- simplifies all hypotheses
  simp [*]


-- you can declare some theorems to be used in simplifying by adding the `@[simp]` tag


-- Split
-- split tactic is useful for breaking nested if-then-else and match expressions in cases


-- -- Extensible Tactics
-- syntax "triv" : tactic -- define new tactic notation
-- macro_rules
--   | `(tactic| triv) => `(tactic| assumption)

-- example (h : p) : p := by
--   triv
