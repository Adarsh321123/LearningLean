open Nat

-- Pattern Matching
-- defining functions from natural numbers to arbitrary types
def sub1 : Nat → Nat
  | zero => zero
  | succ x => x

def isZero : Nat → Bool
  | zero => true
  | succ x => false

example (x : Nat) : sub1 (succ x) = x := rfl

def swap : α × β → β × α
  | (a, b) => (b, a)

def foo : Nat × Nat → Nat
  | (m, n) => m + n

def bar : Option Nat → Nat
  | some n => n + 1
  | none => 0

namespace hidden
def not : Bool → Bool
  | true => false
  | false => true

theorem not_not : ∀ (b : Bool), not (not b) = b
  | true => rfl
  | false => rfl

def sub2 : Nat → Nat
  | 0 => 0
  | 1 => 0
  | x+2 => x

example : sub2 (x + 2) = x := rfl
example : sub2 5 = 3 := rfl

-- can use `_` if the value of an argument is not needed (wildcard pattern or anonymous variable)
def tail2 : {α : Type u} → List α → List α
  -- `α` does not participate in case split
  | α, [] => []
  | α, a :: as =>  as

end hidden


-- Wildcards and Overlapping Patterns
namespace Hidden
-- we can turn this
def foo : Nat → Nat → Nat
  | 0, n => 0
  | m + 1, 0 => 1
  | m + 1, n + 1 => 2
-- into this using overlapping patterns
def foo2 : Nat → Nat → Nat
  | 0, n => 0
  | m, 0 => 1
  | m, n => 2
-- or using wildcards
def foo3 : Nat → Nat → Nat
  | 0, _ => 0
  | _, 0 => 1
  | _, _ => 2

-- with `Option α`, can use `some a` for provided patterns and `none` for incomplete cases
def f2 : Nat → Nat → Option Nat
  | 0, _ => some 1
  | _, 0 => some 2
  | _, _ => none
end Hidden


-- Structural Recursion and Induction
-- structural recursion is where arguments on right side of `=>` are subterms of patterns on the left
namespace Hidden
def add : Nat → Nat → Nat
  | m, zero => m
  | m, succ n => succ (add m n)

def fib : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

example : fib 7 = 21 := rfl
end Hidden


-- Well-Founded Recursion and Induction
-- if there is no `termination_by`, a well-founded relations is
-- derived by selecting an argument and using typeclass resolution to synthesize a well-founded relation
-- if it is specified, maps arguments of function to type `α` and typeclass resolution used
-- default well-founded relation instance for `Nat` is `<`
-- `decreasing_tactic` shows that recursive applications are smaller with respect to well-founded relation


-- Mutual Recursion
namespace Hidden
mutual
  def even : Nat → Bool
    | 0 => true
    | n + 1 => odd n

  def odd : Nat → Bool
    | 0 => false
    | n + 1 => even n
end

theorem even_eq_not_odd : ∀ a, even a = not (odd a) := by
  intro a
  induction a
  · simp [even, odd]
  · simp [even, odd, *]
end Hidden
