-- Type theory refers to the fact that every expression has its own type
-- we will declare objects and check their types
def m : Nat := 1
def n : Nat := 0
def b1 : Bool := true
def b2 : Bool := false

-- a `#` usually indicates querying the system for information
#check m
#check n
#check n + 0
#check m * (n + 0)
#check b1
#check b1 && b2
#check b1 || b2
#check true

#eval 5 * 4
#eval m + 2
#eval b1 && b2


-- we can define new types out of others
#check Nat → Nat
#check Nat × Nat
#check Nat → Nat → Nat
#check Nat → (Nat → Nat)
#check (Nat → Nat) → Nat  -- called a "functional"
#check Nat × Nat → Nat

#check Nat.succ
#check Nat.add  -- takes a natural number, returns a function which takes another natural number, returns a natural number
#check Nat.add 3  -- type of functions that take a natural number and return a natural number
#check Nat.add 2 5


-- types themselves are objects, so each of them also has a type
#check Nat  -- Type
#check Bool  -- Type
#check Nat × Bool  -- Type


-- let's define new constants for types
def α : Type := Nat
def β : Type := Bool
def F : Type → Type := List  -- List α denotes lists of the elements of α
def G : Type → Type → Type := Prod


#check α  -- Type
#check F α  -- Type
#check G α  -- Type → Type
#check Prod α β  -- Type
#check List α  -- Type


-- Lean has an infinite hierarchy of types
#check Type  -- Type 1
#check Type 1  -- Type 2
#check Type 2  -- Type 3
#check List  -- Type u → Type u (List is polymorphic meaning it should work for any type)

universe u  -- declare universe variables
def H (α : Type u) : Type u := Prod α α
#check H  -- Type u → Type u


-- can use `fun` or `λ` to create a function from an expression
#check fun (x : Nat) => x + 5  -- Nat → Nat
#check λ (x : Nat) => x + 5
#check λ x : Nat => x + 5  -- Nat inferred

#eval (λ x : Nat => x + 5) 10  -- 15
#check fun x y => if not y then x + 1 else x + 2  -- Nat → Bool → Nat (first two types inferred)
-- generally, Lean can infer the type annotation


-- Definitions
def double (x : Nat) : Nat :=
  x + x

def double_lambda :=
  fun (x : Nat) => x + x

#eval double 3

def pi := 3.141592654


def doTwice (f : Nat → Nat) (x : Nat) : Nat :=
  f (f x)

#eval doTwice double 2


def compose (α β γ : Type) (g : β → γ) (f : α → β) (x : α) : γ :=
  g (f x)

def square (x : Nat) : Nat :=
  x * x

#eval compose Nat Nat Nat double square 3


-- Local Definitions
#eval let y := 2 * 2; y * y


-- Variables and Sections
variable (α β γ : Type)
variable (x : α)
section useful
  -- variables declared here can only be used in this scope
  -- you can also nest sections
  -- you also don't have to name sections
end useful


-- Namespaces
namespace Foo
  -- can group definitions
  -- you need to name namespaces (lol)
  -- once closed, namespaces can be reopened, even in other files
end Foo

-- these are in the namespace List
#check List.nil
#check List.cons
#check List.map

open List
#check nil
#check cons
#check map


-- Dependent Type Theory
-- types depend on their arguments (`List Nat` is different from `List Bool`)
-- can also make functions where the type of the output depends on the input
-- can make depends pairs using `⟨a,b⟩` or `Sigma.mk a b` or `(a : α) × β a` (generalizes `a × b`)
def ident {α : Type u} (x : α) := x  -- brackets makes the first argument implicit
#check ident 1
#check @id Nat -- an argument to `id` is implicit, but we want to provide the argument explicitly
