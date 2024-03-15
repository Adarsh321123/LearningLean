-- everything follows from type universes, dependent type arrows, and inductive types
-- structure/record: non-recursive inductive type containing only one constructor
-- structure also has projection to destruct an instance of a structure and retrieve value stored in its fields
-- examples: `prod.fst` and `prod.snd`


-- Declaring Structures
-- structure <name> <parameters> <parent-structures> where
--   <constructor> :: <fields>

structure Point (α : Type u) where
  mk :: (x : α) (y : α)
  deriving Repr

#check Point  -- Type
#check @Point.rec -- eliminator
#check @Point.mk -- constructor
#check @Point.x   -- projection
#check @Point.y  -- projection

open Point
example (a b : α) : x (mk a b) = a :=
  rfl

def Point.smul (n : Nat) (p : Point Nat) :=
  Point.mk (n * p.x) (n * p.y)

def p : Point Nat := Point.mk 1 2

#eval p.smul 3

-- `List.map` takes a list as its second non-implicit argument
#check @List.map

def xs : List Nat := [1, 2, 3]
def f : Nat → Nat := fun x => x * x

-- interpreted as `List.map f xs`
#eval xs.map f  -- [1, 4, 9]


-- Inheritance
-- we define a struct using multiple inheritance and then define an object
namespace Hidden

structure Point (α : Type u) where
  x : α
  y : α
  z : α

structure RGBValue where
  red : Nat
  green : Nat
  blue : Nat

structure RedGreenPoint (α : Type u) extends Point α, RGBValue where
  no_blue : blue = 0

def p : Point Nat :=
  { x := 10, y := 10, z := 20 }

def rgp : RedGreenPoint Nat :=
  { p with red := 200, green := 40, blue := 0, no_blue := rfl }

example : rgp.x = 10 := rfl
example : rgp.red = 200 := rfl

end Hidden
