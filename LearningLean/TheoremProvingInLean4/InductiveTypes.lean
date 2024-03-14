import Mathlib
open Real
-- every concrete type besides universes and every type constructor besides dependent arrows is inductive type
-- inductive type is built from specified list of constructors

-- inductive Foo where
--   | constructor₁ : ... → Foo
--   | constructor₂ : ... → Foo
--   ...
--   | constructorₙ : ... → Foo

-- each constructor describes a new way of building an object of type Foo, possibly from previous values
-- every inductive type comes with introduction rules (show how to construct an element of that type) and
-- elimination rules (shows how to use elements of that type in another construction)
-- introduction rule here is the constructor
-- elimination rules provide a principle of recursion which includes as a special case a principle of induction


-- Enumerated Types
-- finite, enumerated list of elements:
-- inductive Weekday where
--   | sunday : Weekday
--   | monday : Weekday
--   | tuesday : Weekday
--   | wednesday : Weekday
--   | thursday : Weekday
--   | friday : Weekday
--   | saturday : Weekday

-- cleaner, since these are distinct elements of Weekday anyway
inductive Weekday where
  | sunday
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  deriving Repr  -- this generates a function that converts Weekday objects into text

-- elimination principle Weekday.rec is defined too and is called a recursor

-- now, the constructors all live in the Weekday namespace
#check Weekday.monday

open Weekday
#check monday


-- match allows us to define a function from Weekday to the natural numbers
-- match is compiled with the Weekday.rec recursor that is generated when you define the inductive type
def numberOfDay (d : Weekday) : Nat :=
  match d with
  | sunday  => 1
  | monday  => 2
  | tuesday => 3
  | wednesday => 4
  | thursday => 5
  | friday => 6
  | saturday => 7

#eval numberOfDay sunday  -- 1
#check @Weekday.rec


-- we can define functions from Weekday to Weekday
namespace Weekday
def next (d : Weekday) : Weekday :=
  match d with
  | sunday    => monday
  | monday    => tuesday
  | tuesday   => wednesday
  | wednesday => thursday
  | thursday  => friday
  | friday    => saturday
  | saturday  => sunday

def previous (d : Weekday) : Weekday :=
  match d with
  | sunday    => saturday
  | monday    => sunday
  | tuesday   => monday
  | wednesday => tuesday
  | thursday  => wednesday
  | friday    => thursday
  | saturday  => friday

#eval next (next tuesday)      -- Weekday.thursday
#eval next (previous tuesday)  -- Weekday.tuesday

example : next (previous tuesday) = tuesday :=
  rfl

end Weekday

-- we can prove the general theorem that `next (previous d) = d`
def next_previous (d : Weekday) : next (previous (d)) = d := by
  cases d <;> rfl

namespace Hidden  -- to avoid conflict with standard library
-- can define `and` using match
def and (a b : Bool) : Bool :=
  match a with
  | true => b
  | false => false
end Hidden


-- Constructors with Arguments
namespace Hidden
inductive Prod (α : Type u) (β : Type v)
  | mk : α → β → Prod α β

inductive Sum (α : Type u) (β : Type v) where
  | inl : α → Sum α β  -- insert left
  | inr : β → Sum α β  -- insert right
end Hidden

def fst {α : Type u} {β : Type v} (p : Prod α β) : α :=
  match p with  -- match interprets `p` as a pair, `Prod.mk a b`
  | Prod.mk a b => a

def prod_example (p : Bool × Nat) : Nat :=
  -- `motive` specifies type of object to construct
  -- `cond b t1 t2` returns `t1` if `b` true and `t2` otherwise
  Prod.casesOn (motive := fun _ => Nat) p (fun b n => cond b (2 * n) (2 * n + 1))

#eval prod_example (true, 3)
#eval prod_example (false, 3)

namespace Hidden2
-- a type with only one constructor can be made with the structure keyword
-- introduces type with constructor `mk`
-- introduces eliminators `rec` and `recOn` and projections `fst` and `snd` too
structure Prod (α : Type u) (β : Type v) where
  mk :: (fst : α) (snd : β)
end Hidden2

structure Color where
  red : Nat
  green : Nat
  blue : Nat
  deriving Repr

def yellow := Color.mk 255 255 0
#eval Color.red yellow  -- 255

namespace Hidden
structure Semigroup where
  carrier : Type u
  mul : carrier → carrier → carrier
  mul_assoc : ∀ a b c, mul (mul a b) c  = mul a (mul b c)
end Hidden


-- Inductively Defined Propositions
namespace Hidden

inductive False : Prop

inductive True : Prop where
  | intro : True

inductive And (a b : Prop) : Prop where
  | intro : a → b → And a b

inductive Or (a b : Prop) : Prop where
  | inl : a → Or a b
  | inr : b → Or a b

inductive Exists {α : Sort u} (p : α → Prop) : Prop where
  | intro (w : α) (h : p w) : Exists p


-- Defining the Natural Numbers
inductive Nat where
  | zero : Nat
  | succ : Nat → Nat
  deriving Repr

#check @Nat.rec

def add (m n : Nat) : Nat :=
  match n with
  | Nat.zero => m
  | Nat.succ n => Nat.succ (add m n)

open Nat

#eval add (succ (succ zero)) (succ zero)
end Hidden


-- Other Recursive Data Types
namespace Hidden

inductive List (α : Type u) where
  | nil : List α
  | cons : α → List α → List α

inductive BinaryTree where
  | leaf : BinaryTree
  | node : BinaryTree → BinaryTree → BinaryTree

end Hidden

-- Tactics for Inductive Types
-- `cases` decomposes the type into its possible constructors
example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (Nat.succ n)) : ∀ n, p n := by
  intro n
  cases n
  · exact hz
  · apply hs

-- example (n : Nat) (h : n ≠ 0) : succ (pred n) = n := by
--   cases n with
--   | zero =>
--     apply absurd rfl h
--   | succ m =>
--     rfl

-- example (p : Nat → Prop) (hz : p 0) (hs : ∀ n, p (succ n)) (m k : Nat) : p (m + 3 * k) := by
--   cases m + 3 * k
--   exact hz
--   apply hs

example (p : Prop) (m n : Nat) (h₁ : m < n → p) (h₂ : m ≥ n → p) : p := by
  cases Nat.lt_or_ge m n
  case inl hlt => exact h₁ hlt
  case inr hge => exact h₂ hge

-- can use `induction` to carry out proofs by induction
namespace hidden
theorem zero_add (n : Nat) : 0 + n = n := by
  induction n with
    | zero => rfl
    | succ n ih => rw [Nat.add_succ, ih]
    -- another option
    -- case zero => rfl
    -- case succ n ih => rw [Nat.add_succ, ih]
end hidden

-- elements of an inductive type have constructors which are injective and have disjoint ranges
-- `injection` tactic makes use of this
-- example (m n k : Nat) (h : succ (succ m) = succ (succ n))
--         : n + k = m + k := by
--   injection h with h'  -- adds `h' : succ m = succ n` to context
--   injection h' with h''  -- add `h'' : m = n` to context
--   rw [h'']


-- Inductive Families
-- inductive family is an indexed family of types defined by a simultaneous induction of the following form:
-- inductive foo : ... → Sort u where
--   | constructor₁ : ... → foo ...
--   | constructor₂ : ... → foo ...
--   ...
--   | constructorₙ : ... → foo ...

namespace hidden
inductive Vector (α : Type u) : Nat → Type u where
  | nil : Vector α 0
  | cons : α → {n : Nat} → Vector α n → Vector α (n + 1)
end hidden


-- Mutual and Nested Inductive Types
-- mutually defined inductive types are two inductive types defined at same time which one referring to the other
namespace hidden
  mutual
    inductive Even : Nat → Prop where
      | even_zero : Even 0
      | even_succ : (n : Nat) → Odd n → Even (n + 1)
  end

  inductive Odd : Nat → Prop where
    | odd_succ : (n : Nat) → Even n → Odd (n + 1)

  -- nested inductive type:
  inductive Tree (α : Type u) where
    -- auto builds isomorphism between `TreeList α` and `List (Tree α)`
    -- defines constructors for `Tree` in terms of the isomorphism
    | mk : α → List (Tree α) → Tree α
end hidden
