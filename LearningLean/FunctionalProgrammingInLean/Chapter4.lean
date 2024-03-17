-- Lean uses type classes, collections of overloadable operations
-- instance is created tat contains implementation of each operation for the new type
-- so type class called `Add` describes types that allow addition, and instance of `Add` for
-- `Nat` provides implementation of addition for `Nat`
-- similar to interface

-- "failed to synthesize instance" is due to an overloaded operation that has not been implemented
-- here, "method" is an operation that has been declared to be overloadable
-- can overload addition using a new type class `Plus` with a method `plus`
class Plus (α : Type) where  -- Plus has type `Type → Type`
  plus : α → α → α  -- takes two arguments and returns something

-- overload for a particular type
instance : Plus Nat where
  plus := Nat.add

open Plus (plus)  -- () means only indicated names in the namespace are accessible
#eval plus 5 3

-- `x+y` is same as `HAdd.hAdd x y`

#check (IO.println)  -- `IO.println : ?m.73 → IO Unit`
-- presence of metavar means Lean did not discover enough type info to find the implicit variables
-- this feature can be suppressed with `@` to understand the signature of the function
#check @IO.println  -- @IO.println : {α : Type u_1} → [inst : ToString α] → α → IO Unit
-- means it accepts an argument of type `α` and there must be a `ToString` instance for `α`, and it returns an IO action

inductive Pos : Type where
  | one : Pos
  | succ : Pos → Pos
  deriving Repr

def addNatPos : Nat → Pos → Pos
  | 0, p => p
  | n + 1, p => Pos.succ (addNatPos n p)

def addPosNat : Pos → Nat → Pos
  | p, 0 => p
  | p, n + 1 => Pos.succ (addPosNat p n)

-- can do heterogenous overloading
instance : HAdd Nat Pos Pos where
  hAdd := addNatPos

instance : HAdd Pos Nat Pos where
  hAdd := addPosNat

instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat → Pos
      | 0 => Pos.one
      | k + 1 => Pos.succ (natPlusOne k)
    natPlusOne n

#eval (3 : Pos) + (5 : Nat)
#eval (3 : Nat) + (5 : Pos)

class HPlus (α : Type) (β : Type) (γ : outParam Type) where  -- `outParam` indicates it is output of the process
  hPlus : α → β → γ

-- `Array α` is dynamically-sized array
-- not possible to mutate a given position; instead a copy is made that has the desired modifications
def northernTrees : Array String :=
  #["sloe", "birch", "elm", "oak"]

#eval northernTrees.size
#eval northernTrees[2]

-- non-empty lists
structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

def idahoSpiders : NonEmptyList String := {
  head := "a",
  tail := [
    "b",
    "c",
    "d",
    "e"
  ]
}

abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length

def NonEmptyList.get (xs : NonEmptyList α) (i : Nat) (ok : xs.inBounds i) : α :=  -- checks that index is valid
  match i with
  | 0 => xs.head
  | n + 1 => xs.tail[n]

-- boolean equality is same as in other languages but there is no separation of reference vs value equality
-- propositional equality is a mathematical statement that admits a proof

namespace Hidden
class Hashable (α : Type) where
  hash : α → UInt64
end Hidden

-- instance deriving like with `deriving Repr` allows compiler to auto construct well-behaved instances of many type classes
-- also good since instances are updated as the definitions of the types evolve

-- polymorphic type called a functor if it has an overload for a function called `map` that transforms every element contained in it by a function
instance : Functor NonEmptyList where
  map f xs := { head := f xs.head, tail := f <$> xs.tail }  -- `<$>` applies a function to each element


-- Coercions
def Pos.toNat : Pos → Nat
  | Pos.one => 1
  | Pos.succ n => n.toNat + 1

namespace Hidden
class Coe (α : Type) (β : Type) where
  coe : α → β

instance : Coe Pos Nat where
  coe x := x.toNat

-- can chain coercions
-- already exists a coercion from Nat to Int, so we can combine with `Coe Pos Nat` to go from `Pos` to `Int`
-- `()` is short for constructor `Unit.unit`

-- inductive A where
--   | a

-- inductive B where
--   | b

-- instance : Coe A B where
--   coe _ := B.b

-- instance : Coe B A where
--   coe _ := A.a

-- instance : Coe Unit A where
--   coe _ := A.a

-- def coercedToB : B := ()

instance : Coe (NonEmptyList α) (List α) where
  coe
    | { head := x, tail := xs } => x :: xs

-- if the ability to coerce depends on the values being coerced, then use dependent coercions
class CoeDep (α : Type) (x : α) (β : Type) where  -- takes the value being coerced as a parameter
  coe : β

instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := { head := x, tail := xs }

-- monoid is some set S, an element s of S, and association binary operator on S s.t. s is neutral on left and right of the operator
-- i.e. naturals, 0, and +

structure Monoid where
  Carrier : Type
  neutral : Carrier
  op : Carrier → Carrier → Carrier

def natMulMonoid : Monoid :=
  { Carrier := Nat, neutral := 1, op := (· * ·)}

def natAddMonoid : Monoid :=
  { Carrier := Nat, neutral := 0, op := (· + ·)}

def foldMap (M : Monoid) (f : α → M.Carrier) (xs : List α) : M.Carrier :=
  let rec go (soFar : M.Carrier) : List α → M.Carrier
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs

end Hidden
