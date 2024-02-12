-- we can express that `r` is transitive
variable (α : Type) (r : α → α → Prop)
variable (trans_r : ∀ x y z, r x y → r y z → r x z)  -- can also make `x y z` implicit using brackets
variable (a b c : α)
variable (hab : r a b) (hbc : r b c)

#check trans_r
#check trans_r a b c
#check trans_r a b c hab
#check trans_r a b c hab hbc


variable (refl_r : ∀ x, r x x)
variable (symm_r : ∀ {x y}, r x y → r y x)
variable (trans_r : ∀ {x y z}, r x y → r y z → r x z)

example (a b c d : α) (hab : r a b) (hcb : r c b) (hcd : r c d) : r a d :=
  trans_r (trans_r hab (symm_r hcb)) hcd


-- Equality
#check Eq.refl
#check Eq.symm
#check Eq.trans


variable (α : Type) (a b c d : α)
variable (hab : a = b) (hcb : c = b) (hcd : c = d)
example : a = d :=
  Eq.trans (Eq.trans hab (Eq.symm hcb)) hcd

-- using projection notation
example : a = d := (hab.trans hcb.symm).trans hcd

example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  Eq.subst h1 h2

example (α : Type) (a b : α) (p : α → Prop)
        (h1 : a = b) (h2 : p a) : p b :=
  h1 ▸ h2

variable (α : Type)
variable (a b : α)
variable (f g : α → Nat)
variable (h₁ : a = b)
variable (h₂ : f = g)

example : f a = f b := congrArg f h₁  -- `congrArg` replaces the argument
example : f a = g a := congrFun h₂ a  -- `congrFun` replaces the function
example : f a = g b := congr h₂ h₁


-- Calculational Proofs
-- this style of proofs is most useful with `simp` and `rw`
variable (a b c d e : Nat)
variable (h1 : a = b)
variable (h2 : b = c + 1)
variable (h3 : c = d)
variable (h4 : e = 1 + d)

theorem T : a = e :=
  calc  -- can be used for any relation which uses transitivity
    a = b := by rw[h1]
    _ = c + 1 := by rw [h2]
    _ = d + 1 := by rw [h3]
    _ = 1 + d := by rw [Nat.add_comm]
    _ = e := by rw [h4]

-- simpler
theorem T_simple : a = e :=
  -- by rw [h1, h2, h3, Nat.add_comm, h4]
  -- `simp` applies given identities repeatedly, previous rules, and commutativity
  by simp [h1, h2, h3, Nat.add_comm, h4]

example (x y : Nat) : (x + y) * (x + y) = x * x + y * x + x * y + y * y :=
  calc
    (x + y) * (x + y) = (x + y) * x + (x + y) * y := by rw [Nat.mul_add]
    _ = x * x + y * x + (x + y) * y := by rw [Nat.add_mul]
    _ = x * x + y * x + (x * y + y * y) := by rw [Nat.add_mul]
    _ = x * x + y * x + x * y + y * y := by rw [← Nat.add_assoc]  -- left arrow means use the identity in the opposite direction


-- Existential Quantifier
example : ∃ x : Nat, x > 0 :=
  have h : 1 > 0 := Nat.zero_lt_succ 0
  ⟨1, h⟩  -- satisfies the introduction rule: we have a term `t` to satisfy the proof of `p t`

-- the existence rulel allows to prove `q` from `∃ x : α, p x` by showing `q` follows from `p w` for arbitrary value `w`
-- if `q` does not mention `w`, then we can show `q` follows from the existence of any such `x`
-- we can use `match` to eliminate from an existential quantifier
variable (α : Type) (p q : α → Prop)
example (h : ∃ x, p x ∧ q x) : ∃ x, q x ∧ p x :=
  match h with
  | ⟨w, hw⟩ => ⟨w, hw.right, hw.left⟩  -- `hw` is `h` with `w` as the argument


def is_even (a : Nat) := ∃ b, a = 2 * b

theorem even_plus_even (h1 : is_even a) (h2 : is_even b) : is_even (a + b) :=
  match h1, h2 with
  | ⟨w1, hw1⟩, ⟨w2, hw2⟩ => ⟨w1 + w2, by rw [hw1, hw2, Nat.mul_add]⟩


-- More on proof language
variable (f : Nat → Nat)
variable (h : ∀ x : Nat, f x <= f (x + 1))

example : f 0 ≤ f 3 :=
  have : f 0 ≤ f 1 := h 0
  have : f 0 ≤ f 2 := Nat.le_trans this (h 1)
  show f 0 ≤ f 3 from Nat.le_trans this (h 2)
