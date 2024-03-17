#eval 1 + 2

-- Lean uses `f x` instead of `f(x)`
#eval String.append "Hello, " "Lean!"

-- no conditional statements, only conditional expressions
-- String.append "it is " (if 1 > 2 then "yes" else "no")
-- since Lean is expression-oriented

-- Lean functions that are applied to only some of their arguments
-- return new functions which wait for the rest of the arguments


-- Types
-- colon operator provides type
#eval (1 + 2 : Nat)
-- Nat represents arbitrarily large unsigned numbers
#eval 1 -2  -- 0


-- Functions and Definitions
def hello := "Hello"
-- new names defined with `:=`
-- equalities with `=`

def lean : String := "Lean"

#eval String.append hello (String.append " " lean)

def add1 (n : Nat) : Nat := n + 1

def maximum (n : Nat) (k : Nat) : Nat :=
  if n < k then
    k
  else
    n

-- returns function signature when name used
#check add1 -- add1 (n : Nat) : Nat

-- all functions actually expect only one argument
-- so `maximum` takes one argument and then returns a new function
-- that functions takes the next argument and continues until no more expected arguments
-- called "currying"


def Str : Type := String
def aStr : Str := "String"

-- works since Types are expressions in Lean


-- Structures
-- Lean does not have mutable state
-- so if replaced `x` of `Point` with `0.0`, then a new `Point` is allocated
-- with `x` field pointing to new value and all other fields pointing to original values from input
structure Point where
  x : Float
  y : Float
deriving Repr


def zeroX (p : Point) : Point :=
  { x := 0, y := p.y }

def zeroXSimpler (p : Point) : Point :=
  { p with x := 0 }  -- all besides `x` stay the same

-- every structure has constructor, which gathers data to be stored in
-- newly-allocated data structure
-- by default, constructor for structure `S` is `S.mk`
-- `S` is namespace qualifier and `mk` is name of constructor
-- accessor function defined for each field of structure
-- so `Point.x` and `Point.y`


-- Datatypes and Patterns
-- datatypes that allow choices are called sum types
-- datatypes that include instances of themselves are called recursive datatypes
-- recursive sum types are called inductive datatypes
-- pattern matching checks which subclass received and then reading values of fields that are available in the given subclass

def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => false

-- Lean ensures that every recursive function will reach a base case


-- Polymorphism
-- in functional programming, means datatypes and definitions that take types as arguments
structure PPoint (α : Type) where
  x : α
  y : α
  deriving Repr

def natOrigin : PPoint Nat :=  -- providing `PPoint` with type `Nat`
  { x := Nat.zero, y := Nat.zero }

namespace Hidden
inductive List (α : Type) where
  | nil : List α
  | cons : α → List α → List α  -- `cons` adds to the front
end Hidden

def explicitPrimesUnder10 : List Nat :=
  List.cons 2 (List.cons 3 (List.cons 5 (List.cons 7 List.nil)))

-- can use `[]` instead of `nil` and `::` instead of `cons`
def length (α : Type) (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | y :: ys => Nat.succ (length α ys)

namespace Hidden
inductive Option (α : Type) : Type where
  | none : Option α
  | some (val : α) : Option α
end Hidden

-- `Prod Nat String` contains `Nat` and `String`
def fives : String × Int := ("five", 5)

def PetName : Type := String ⊕ String

def howManyDogs (pets : List PetName) : Nat :=
  match pets with
  | [] => 0
  | Sum.inl _ :: morePets => howManyDogs morePets + 1
  | Sum.inr _ :: morePets => howManyDogs morePets

-- can use `Unit` for placeholder for missing data
-- can use as void


-- Additional Conveniences
-- no need to list all implicit arguments
-- so can do this without listing `{α : Type}`
-- namespace Hidden
-- def length (xs : List α) : Nat :=
--   match xs with
--   | [] => 0
--   | y :: ys => Nat.succ (length ys)
-- end Hidden

-- instead of this
-- def id1 (x : α) : α := x
-- Lean can infer type so can do this
-- def id2 (x : α) := x


-- instead of
-- fun k => k + 1
-- can do
-- (· + 1), where · stands for an argument

-- positional structure arguments:
#eval (⟨1, 2⟩ : Point)

-- string interpolation using `!` before the string
