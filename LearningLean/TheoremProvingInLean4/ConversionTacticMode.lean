-- inside tactic block, use `conv` to enter conversion mode
-- can travel inside assumptions, goal, function abstractions, and dependent arrows to apply rewriting or simplifying steps


-- Basic Navigation and Rewriting
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv =>
    lhs  -- navigates to left of equality
    congr  -- creates as many targets as there are arguments to current head function (mult here)
    rfl  -- closes first target
    rw [Nat.mul_comm]

-- can also rewrite under binders
example : (fun x : Nat => 0 + x) = (fun x => x) := by
  conv =>
    lhs
    intro x  -- navigation command entering inside the `fun` binder
    rw [Nat.zero_add]


-- Pattern Matching
example (a b c : Nat) : a * (b * c) = a * (c * b) := by
  conv in b * c => rw [Nat.mul_comm]
  -- same as
  -- conv =>
  --   pattern b * c
  --   rw [Mat.mul_comm]
