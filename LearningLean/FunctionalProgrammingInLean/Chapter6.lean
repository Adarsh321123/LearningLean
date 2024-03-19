-- every monad is a functor
-- not every functor is a monad

-- in multiple inheritance, if two parents have the same attribute (diamond problem), then Lean chooses the first one specified
-- there is also type class inheritance since each type class is a structure behind the scenes


-- Applicative Functors
-- functor that also has `pure` and `seq`
-- pure is same as in `Monad` and `seq` is same as `map`


-- Applicative Contract
-- applicative functor should respect identity, `pure id <*> v = v`
-- respect function composition, `pure (· ∘ ·) <*> u <*> v <*> w = u <*> (v <*> w)`
-- sequencing pure operations should be a no-op, so `pure f <*> pure x = pure (f x)`
-- ordering of pure operations does not matter, so `u <*> pure = pure (fun f => f x) <*> u`


-- Universes
-- type that classifies other types
-- `Type` and `Prop` are examples
-- `Type` cannot have a type of `Type` in order to remove paradoxes
#check Type  -- `Type 1`

namespace Hidden
class Bind (m : Type u → Type v) where
  bind : {α β : Type u} → m a → (α → m β) → m β

-- class Monad (m : Type u → Type v) extends Applicative m, Bind m : Type (max (u + 1) v) where
--   map f x := bind x (Function.comp pure f)
--   seq f x := bind f fun y => Functor.map y (x ())
--   seqLeft x y := bind x fun a => bind (y ()) (fun _ => pure a)
--   seqRight x y := bind x fun _ => y ()
end Hidden
