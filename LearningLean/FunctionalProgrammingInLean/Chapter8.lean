-- dependent types are types that contain non-type expressions

def natOrStringThree (b : Bool) : if b then Nat else String :=
  match b with
  | true => (3 : Nat)
  | false => "three"

-- allowing return types to branch on argument values gives flexibility
-- also enables strict invariants at compile time


-- Indexed Families
-- inductive types where arguments vary based on the choice of the constructor
-- varying arguments are called indices
inductive Vect (α : Type u) : Nat → Type u where
  | nil : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)

def Vect.replicate (n : Nat) (x : α) : Vect α n :=
  match n with
  | 0 => .nil
  | k + 1 => .cons x (replicate k x)

-- type class allows extending the type system with new rules
-- universe allows keeping the types the same in that category

-- parameters appear before a colon and indices are after
-- can be seen in `Vect` definition
-- universe level of datatype is at least as large as largest parameter and strictly larger than largest index


-- Definitional equality is an underapproximation of equality that essentially checks for equality of
-- syntactic representation modulo computation and renaming of bound variables. Lean automatically checks
-- for definitional equality in situations where it is required.
-- Propositional equality must be explicitly proved and explicitly invoked by the programmer. In return,
-- Lean automatically checks that the proofs are valid and that the invocations accomplish the right goal.
