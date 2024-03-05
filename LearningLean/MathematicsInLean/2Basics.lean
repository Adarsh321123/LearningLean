import Mathlib
import LeanCopilot
open Real

example (a b c : ℝ) : a * b * c = b * (a * c) := by
  rw [mul_comm a b]
  rw [mul_assoc]


-- left arrow indicates going in the reverse direction of an identity
example (a b c : ℝ) : c * b * a = b * (a * c) := by
  rw [mul_assoc, mul_comm, mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc]
  rw [mul_comm a b]
  rw [mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (c * a) := by
  rw [mul_comm, mul_assoc]

example (a b c : ℝ) : a * (b * c) = b * (a * c) := by
  rw [← mul_assoc, mul_comm a, mul_assoc]

example (a b c d e f : ℝ) (h : b * c = e * f) : a * b * c * d = a * e * f * d := by
  rw [mul_assoc a b c, h, ← mul_assoc]

example (a b c d : ℝ) (hyp : c = b * a - d) (hyp' : d = a * b) : c = 0 := by
  rw [hyp, hyp', mul_comm, sub_self]

-- expression that begins with `calc` is a proof term and so does not need `by`
-- one way to write these proofs is to use `sorry` for justificatoin, make sure Lean accepts expressions, and then prove these steps
variable (a : ℝ)
example : (a + b) * (c + d) = a * c + a * d + b * c + b * d :=
  -- using `rw` proof
  -- rw [mul_add, add_mul, add_mul, ← add_assoc, add_assoc (a * c), add_comm (b * c) (a * d), ← add_assoc]
  -- using `calc`
  calc
    (a + b) * (c + d) = a * c + b * c + (a * d + b * d) := by rw [mul_add, add_mul, add_mul]
    _ = a * c + (b * c + a * d) + b * d := by rw [← add_assoc, add_assoc (a * c)]
    _ = a * c + a * d + b * c + b * d := by rw [add_comm (b * c) (a * d), ← add_assoc]

example (a b : ℝ) : (a + b) * (a - b) = a ^ 2 - b ^ 2 := by
  rw [add_mul]
  rw [mul_sub]
  rw [mul_sub]
  rw [add_sub]
  rw [← pow_two, ← pow_two]
  rw [mul_comm]
  ring

-- can also rewrite in an assumption
example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp'] at hyp
  rw [mul_comm d a] at hyp
  rw [← two_mul (a * d)] at hyp
  rw [← mul_assoc 2 a d] at hyp
  exact hyp

-- `ring` can only be used when something follows from ring axioms without any local assumptions
example : c * b * a = b * (a * c) := by
  ring

example : (a + b) * (a + b) = a * a + 2 * (a * b) + b * b := by
  ring

example (a b c d : ℝ) (hyp : c = d * a + b) (hyp' : b = a * d) : c = 2 * a * d := by
  rw [hyp, hyp']
  ring

example (a b c : ℕ) (h : a + b = c) : (a + b) * (a + b) = a * c + b * c := by
  nth_rw 2 [h]  -- replaces the second occurence of `c`
  rw [add_mul]

variable (R: Type*) [CommRing R]  -- all our old proofs will hold with using commutative rings instead of the reals

-- `open` opens a namespace

-- useful theorem from `Mathlib`:
-- theorem neg_add_cancel_left (a b : ℝ) : -a + (a + b) = b := by
--   rw [← add_assoc, add_left_neg, zero_add]

theorem mul_zero (a : R) : a * 0 = 0 := by
  have h : a * 0 + a * 0 = a * 0 + 0 := by
    rw [← mul_add, add_zero, add_zero]
  rw [add_left_cancel h]

theorem zero_mul (a : ℝ) : 0 * a = 0 := by
  rw [mul_comm]
  exact mul_zero a

theorem neg_neg_mine (a : R) : - - a = a := by
  simp

example (a b : R) : a - b = a + -b :=
  sub_eq_add_neg a b

example (a b : ℝ) : a - b = a + -b :=
  rfl  -- defined for reals

theorem self_sub (a : R) : a - a = 0 := by
  rw [sub_eq_zero]

theorem one_add_one_eq_two_mine : 1 + 1 = (2 : R) := by
  norm_num  -- normalizes numerical expressions


theorem two_mul_mine (a : R) : 2 * a = a + a := by
  ring

variable (a b c d : ℝ)
#check (le_refl : ∀ a : ℝ, a ≤ a)
#check (le_trans : a ≤ b → b ≤ c → a ≤ c)

-- `apply` (1) takes the proof, (2) matches its conclusion with the
-- goal, and (3) leaves the hypothesis as new goals

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z := by
  apply le_trans  -- cases: `x ≤ ?b` and `?b ≤ z`
  · apply h₀
  · apply h₁

example (x y z : ℝ) (h₀ : x ≤ y) (h₁ : y ≤ z) : x ≤ z :=
  le_trans h₀ h₁

example (x : ℝ) : x ≤ x :=
  le_refl x

#check (lt_of_le_of_lt : a ≤ b → b < c → a < c)
#check (lt_of_lt_of_le : a < b → b ≤ c → a < c)
#check (lt_trans : a < b → b < c → a < c)
#check (log_le_log : 0 < a → a ≤ b → log a ≤ log b)
#check (log_lt_log : 0 < a → a < b → log a < log b)
#check (exp_pos : ∀ a, 0 < exp a)

example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  exact lt_trans (lt_of_lt_of_le (lt_of_le_of_lt h₀ h₁) h₂) h₃

example (h₀ : a ≤ b) (h₁ : b < c) (h₂ : c ≤ d) (h₃ : d < e) : a < e := by
  linarith  -- handles linear arithmetic

example (h : 2 * a ≤ 3 * b) (h' : 1 ≤ a) (h'' : d = 2) : d + a ≤ 5 * b := by
  linarith

-- `linarith` can also use additional inequalities passed as arguments
example (h : 1 ≤ a) (h' : b ≤ c) : 2 + a + exp b ≤ 3 * a + exp c := by
  linarith [exp_le_exp.mpr h']  -- says `exp b ≤ exp c`

#check (exp_le_exp : exp a ≤ exp b ↔ a ≤ b)
#check (exp_lt_exp : exp a < exp b ↔ a < b)
#check (add_lt_add_of_le_of_lt : a ≤ b → c < d → a + c < b + d)
#check (add_lt_add_of_lt_of_le : a < b → c ≤ d → a + c < b + d)

example (h₀ : a ≤ b) (h₁ : c < d) : a + exp c + e < b + exp d + e := by
  apply add_lt_add_of_lt_of_le
  · apply add_lt_add_of_le_of_lt h₀
    apply exp_lt_exp.mpr h₁
  apply le_refl

example (h₀ : d ≤ e) : c + exp (a + d) ≤ c + exp (a + e) := by
  apply add_le_add_left
  rw [exp_le_exp]
  apply add_le_add_left
  exact h₀

example : (0 : ℝ) < 1 := by norm_num

example (h : a ≤ b) : log (1 + exp a) ≤ log (1 + exp b) := by
  have h₀ : 0 < 1 + exp a := by
      positivity
  apply log_le_log h₀
  apply add_le_add_left
  rw [exp_le_exp]
  exact h

example : 0 ≤ a^2 := by
  exact sq_nonneg a

example (h : a ≤ b) : c - exp b ≤ c - exp a := by
  apply sub_le_sub_left
  rw [exp_le_exp]
  exact h

-- Mathlib favors `≤` over `≥`
example : 2 * a * b ≤ a ^ 2 + b ^ 2 := by
  have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2
  calc
    a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
    _ ≥ 0 := by apply pow_two_nonneg
  linarith

#check abs_le'.mpr

-- `constructor` splits a conjunction into two goals
example : |a * b| ≤ (a ^ 2 + b ^ 2) / 2 := by
  apply abs_le'.mpr
  constructor
  · have h : 0 ≤ a ^ 2 - 2 * a * b + b ^ 2
    calc
      a ^ 2 - 2 * a * b + b ^ 2 = (a - b) ^ 2 := by ring
      _ ≥ 0 := by apply pow_two_nonneg
    linarith
  · have h : 0 ≤ a ^ 2 + 2 * a * b + b ^ 2
    calc
      a ^ 2 + 2 * a * b + b ^ 2 = (a + b) ^ 2 := by ring
      _ ≥ 0 := by apply pow_two_nonneg
    linarith

#check (min_le_left a b : min a b ≤ a)
#check (min_le_right a b : min a b ≤ b)
#check (le_min : c ≤ a → c ≤ b → c ≤ min a b)
#check le_antisymm

example : min a b = min b a := by
  apply le_antisymm
  · apply le_min
    · apply min_le_right
    · apply min_le_left
  · apply le_min
    · apply min_le_right
    · apply min_le_left

example : min a b = min b a := by
  apply le_antisymm
  repeat  -- applies as many times as possible
    apply le_min
    apply min_le_right
    apply min_le_left

variable (m n : ℕ)

#check (Nat.gcd_zero_right n : Nat.gcd n 0 = n)
#check (Nat.gcd_zero_left n : Nat.gcd 0 n = n)
#check (Nat.lcm_zero_right n : Nat.lcm n 0 = 0)
#check (Nat.lcm_zero_left n : Nat.lcm 0 n = 0)

example : Nat.gcd m n = Nat.gcd n m := by
  rw [Nat.gcd_comm]

-- Partial Order is a set with a binary relation that is reflexive, transitive, and antisymmetric (like `≤` on the real numbers)
variable {α : Type*} [PartialOrder α]  -- use Greek letters for types and letters for algebraic structures like rings or groups
variable (x y z : α)

#check x ≤ y
#check (le_refl x : x ≤ x)
#check (le_trans : x ≤ y → y ≤ z → x ≤ z)
#check (le_antisymm : x ≤ y → y ≤ x → x = y)

-- strict partial order is `<`
#check x < y
#check (lt_irrefl x : ¬x < x)
#check (lt_trans : x < y → y < z → x < z)
#check (lt_of_le_of_lt : x ≤ y → y < z → x < z)
#check (lt_of_lt_of_le : x < y → y ≤ z → x < z)

example : x < y ↔ x ≤ y ∧ x ≠ y :=
  lt_iff_le_and_ne

-- lattice is a structure that extends a partial order with operations `⊓` and `⊔`
variable {α : Type*} [Lattice α]
variable (x y z : α)

#check x ⊓ y  -- greatest lower bound
#check (inf_le_left : x ⊓ y ≤ x)
#check (inf_le_right : x ⊓ y ≤ y)
#check (le_inf : z ≤ x → z ≤ y → z ≤ x ⊓ y)
#check x ⊔ y  -- least upper bound
#check (le_sup_left : x ≤ x ⊔ y)
#check (le_sup_right : y ≤ x ⊔ y)
#check (sup_le : x ≤ z → y ≤ z → x ⊔ y ≤ z)
