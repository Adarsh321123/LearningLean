import Mathlib
open Real

-- importing is transitive

-- this definition is treated as a macro
-- def Foo.bar : Nat := 1

-- expands to
namespace Foo
def bar : Nat := 1
end Foo

-- `_root_` is the description of an empty prefix
-- can prevent creating a shorter alias using the `protected` keyword
-- `export` aliases one namespace to another
export Nat (succ add sub)  -- creates aliases for `succ`, `add`, and `sub` in the current namespace
-- whenever the namespace is open, these aliases are available


-- Attributes
-- attribute remains in effect in any file that imports one in which the declaration occurs
def isPrefix (l₁ : List α) (l₂ : List α) : Prop :=
 ∃ t, l₁ ++ t = l₂

theorem List.isPrefix_self (as : List α) : isPrefix as as :=
  ⟨[], by simp⟩  -- says we can concatentate `as` with `[]` to get `as`, true by `simp`

attribute [simp] List.isPrefix_self  -- this means we should use this theorem when simplifying expressions involving `isPrefix`

-- adding the local modifier restricts the scope
section
attribute [local simp] List.isPrefix_self
end


-- Notations and Precedence
-- fixity, parsing precedence, token, function the token is translated to

infixl:65   " + " => HAdd.hAdd  -- left-associative
infix:50    " = " => Eq         -- non-associative
infixr:80   " ^ " => HPow.hPow  -- right-associative
prefix:100  "-"   => Neg.ne
postfix:max "⁻¹"  => Inv.inv


-- Coercions
-- Int is different from Nat, but Int.ofNat views Nat as Int
variable (m n : Nat)
variable (i j : Int)
#check i + m


-- Setting options
-- set_option pp.explicit true  -- displays implicit arguments
-- set_option pp.universes true  -- displays hidden universe parameters
-- set_option pp.notation false  -- display output using defined notation

-- #check 2 + 2 = 4
-- #reduce (fun x => x + 2) = (fun x => x + 3)
-- #check (fun x => x + 1) 1


-- Using the library
-- in each file, you need to open the namespaces you wish to use
-- https://github.com/leanprover/lean4/tree/master/src/Init
-- https://github.com/leanprover/std4/tree/main/Std
-- identifiers are usually camelCase
-- types are usually CamelCase
-- theorems are descriptive names where the different components are separated by underscores
-- since propositions are types, we can use dot notation for logical connectives:
#check @And.intro
#check @Or.inl


-- Auto Bound Implicit Arguments
-- functions with implicit arguments are verbose sometimes:
-- universe u v w
-- def compose {α : Type u} {β : Type v} {γ : Type w}
--             (g : β → γ) (f : α → β) (x : α) : γ :=
--     g (f x)

-- instead, any unbound identifier is added as an implicit argument if it is a single lower case letter or greek letter
def compose (g : β → γ) (f : α → β) (x : α) : γ :=
    g (f x)

#check @compose
