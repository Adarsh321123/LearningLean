-- Propositional Extensionality
namespace Hidden
axiom propext {a b : Prop} : (a ↔ b) → a = b

theorem thm₂ (a b : Prop) (p : Prop → Prop) (h : a ↔ b) (h₁ : p a) : p b :=
  propext h ▸ h₁

end Hidden


-- Function Extensionality
-- any two functions of type `(x : α) → β x` that agree on all their inputs are equal

-- Quotient
-- If `α` is any type and `r` is an equivalence relation on `α`, then the quotient is `α / r`


-- Choice
universe u
-- produces element of `α` given assertion `h` that `α` is nonempty
axiom choice {α : Sort u} : Nonempty α → α


-- Law of Excluded Middle
open Classical
#check (@em : ∀ (p : Prop), p ∨ ¬p)
