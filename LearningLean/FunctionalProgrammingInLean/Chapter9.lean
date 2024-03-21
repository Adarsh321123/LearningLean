def Nat.plusR : Nat → Nat → Nat
  | n, 0 => n
  | n, k + 1 => plusR n k + 1

-- tactics are like powerful macros -- they generate the program
theorem plusR_zero_left (k : Nat) : k = Nat.plusR 0 k := by
  induction k with -- constructs recursive function that corresponds to the induction
  | zero => rfl
  | succ n ih =>
    unfold Nat.plusR -- `n` and `ih` are the two assumptions given to us (the thing we are trying to prove is technically the type)
    rw [← ih]


theorem plusR_zero_left_simple (k : Nat) : k = Nat.plusR 0 k := by
  -- dropping `with` just gives a proof state with two goals
  induction k -- constructs recursive function that corresponds to the induction
  case zero => rfl
  case succ n ih =>
    simp [Nat.plusR]
    assumption  -- solves if any assumption matches


theorem plusR_zero_left_simple_2 (k : Nat) : k = Nat.plusR 0 k := by
  -- dropping `with` just gives a proof state with two goals
  induction k <;> simp [Nat.plusR] <;> assumption


inductive BinTree (α : Type) where
  | leaf : BinTree α
  | branch : BinTree α → α → BinTree α → BinTree α  -- value of `α` for current node, and a left and right node

def BinTree.count : BinTree α → Nat
  | .leaf => 0
  | .branch l _ r =>
    1 + l.count + r.count

def BinTree.mirror : BinTree α → BinTree α
  | .leaf => .leaf
  | .branch l x r => .branch (mirror r) x (mirror l)

theorem BinTree.mirror_count (t : BinTree α) : t.mirror.count = t.count := by
  induction t
  case leaf => rfl
  case branch l x r lm lr =>
    simp [BinTree.mirror, BinTree.count]
    rw [lm, lr]
    simp_arith  -- useful for arithmetic identities

theorem BinTree.mirror_count_simple (t : BinTree α) : t.mirror.count = t.count := by
  induction t
  case leaf => rfl
  case branch l x r lm lr =>
    simp_arith [BinTree.mirror, BinTree.count, *]  -- `*` uses all assumptions available

theorem BinTree.mirror_count_simple_2 (t : BinTree α) : t.mirror.count = t.count := by
  induction t <;> simp_arith [BinTree.mirror, BinTree.count, *]
