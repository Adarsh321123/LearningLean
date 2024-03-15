namespace hidden
class Add (a : Type) where
  add : a → a → a

#check @Add.add  -- instance implicit (synthesized using typeclass resolution)

def double [Add a] (x : a) : a :=
  Add.add x x

end hidden


-- Chaining instances
-- instance declaration can depend on an implicit instance of a type class
instance [Inhabited a] [Inhabited b] : Inhabited (a × b) where
  default := (default, default)

#eval (default : Nat × Bool)


-- ToString
structure Person where
  name : String
  age : Nat

instance : ToString Person where
  toString p := p.name ++ "@" ++ toString p.age

#eval toString { name := "Leo", age := 542 : Person }


-- Numeral
structure Rational where
  num : Int
  den : Nat
  inv : den ≠ 0

instance : OfNat Rational n where
  ofNat := { num := n, den := 1, inv := by decide }


-- Local Instances
structure Point where
  x : Nat
  y : Nat

section

local instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

def double (p : Point) :=
  p + p

end


-- Scoped Instances
-- only active when inside of namespace or open the namespace
namespace Point

scoped instance : Add Point where
  add a b := { x := a.x + b.x, y := a.y + b.y }

end Point


-- Decidable Propositions
-- `Prop` is decidable if we can say it is True or False
-- open Classical
-- at this point, `Decidable p` has an instance for every `p`
-- `decide` uses `Decidable` instance to solve simple goals
example : 10 < 5 ∨ 1 > 0 := by
  decide  -- tries to infer decision procedure


-- Coercions
-- we define coercion from `α` to `β` by declaring an instance of `Coe α β`
instance : Coe Bool Prop where
  coe b := b = true

#eval if true then 5 else 3
