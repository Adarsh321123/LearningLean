-- This chapter focuses on writing assertions and proofs

-- `Prop` is the type for propositions, and we can use constructores to build propositions from others
#check And  -- Prop → Prop → Prop
#check Or
#check Not  -- Prop → Prop

variable (p q r : Prop)
#check And p q  -- Prop
#check Or (And p q) r  -- Prop
#check (And p q) → (And p q)

axiom and_comm (p q : Prop) : (And p q) → (And q p)
variable (p q : Prop)
#check and_comm p q

-- Rule of modus ponens: From a proof of `p → q` and a proof of `p`, we have a proof of `q`
axiom modus_ponens : (p q : Prop) → (p → q) → p → q

-- To express a formal assertion, we need `p : Prop`. To prove the assertion, we need `t: p`. Lean helps us construct `t` and verify it is well-formed and has the correct type


-- Propositions as Types
variable {p : Prop}
variable {q : Prop}
-- theorem t1 : p → q → p := fun hp : p => fun hq : q => hp  -- `hp : p` and `hq : q` can be viewed as assumptions
-- #print t1

-- theorem t1 : p → q → p :=
--   fun hp : p =>
--   fun hq : q =>
--   show p from hp  -- can specify type of `hp` with `show`

-- axiom hp : p  -- postulates existence of an element of the given type
-- theorem t2 : q → p := t1 hp

theorem t1 (p q : Prop) (hp : p) (hq : q) : p := hp

variable (p q r s : Prop)

#check t1 p q  -- p → q → p
#check t1 r s  -- r → s → r
#check t1 (r → s) (s → r)  -- (r → s) → (s → r) → (r → s)

-- `example` states a theorem without naming it or storing it in the permanent context
example (p q : Prop) (h : p ∧ q) : q ∧ p :=
  And.intro (And.right h) (And.left h)

variable (hp : p) (hq : q)
#check (⟨hp, hq⟩ : p ∧ q)  -- anonymous constructor notation can be used on inductive types that can be inferred from context

-- simpler:
example (p q : Prop) (h : p ∧ q) : q ∧ p :=
  ⟨h.right, h.left⟩

-- Negation and Falsity
-- `¬p` is defined as `p → False`, meaning we derive a contradiction from `p`
variable (p q : Prop)
-- given `p` implies `q` and `q` is not true, we will prove that `p` is not true
example (hpq : p → q) (hnq : ¬q) : ¬p :=
  fun hp : p =>  -- given `hp`, a proof of `p`
  -- `hpq hp` gives a proof of `q`
  -- it is a contradiction to apply a proof that `q` is false to a proof that `q` is true
  show False from hnq (hpq hp)
  -- overall, to prove `¬p`, we assume `p` and show this leads to a contradiction

example (p q r : Prop) (hnp : ¬p) (hq : q) (hqp : q → p) : r :=
  absurd (hqp hq) hnp  -- `absurd` means we derive an arbitrary fact from contradictory hypotheses


-- Logical Equivalence
theorem and_swap (p q : Prop) : p ∧ q ↔ q ∧ p :=
  Iff.intro
    (fun h : p ∧ q =>
    show q ∧ p from And.intro (And.right h) (And.left h))
    (fun h : q ∧ p =>
    show p ∧ q from And.intro (And.right h) (And.left h))

-- simpler
theorem and_swap_simple (p q : Prop) : p ∧ q ↔ q ∧ p :=
  ⟨ fun h => ⟨h.right, h.left⟩, fun h => ⟨h.right, h.left⟩ ⟩

example (h : p ∧ q) : q ∧ p := (and_swap p q).mp h  -- `mp` is forward direction and `mpr` is backward direction


-- Subgoals
-- can use `have` to create subgoals
example (h : p ∧ q) : q ∧ p :=
  have hp : p := h.left
  suffices hq : q from And.intro hq hp  -- first, we need to show it suffices to just show `q`
  show q from h.right  -- then, we need to show `q`


-- Classical Logic
open Classical
variable (p : Prop)
#check em p  -- p ∧ ¬p

example (h : ¬¬p) : p :=
  byContradiction
    (fun h1 : ¬p =>
    show False from h h1)
