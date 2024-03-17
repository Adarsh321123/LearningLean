def woodlandCritters : List String :=
  ["hedgehog", "deer", "snail"]

def hedgehog := woodlandCritters[0]
#eval hedgehog

-- when a proposition is proven, it is called a theorem
-- tactics are small programs that construct evidence for a proposition
-- running a tactic on a goal results in a new proof state that contain new goals
-- `simp` can prove theorems that use connectives true, false, and, or, implies, not
-- `def third (xs : List α) : α := xs[2]` is bad since could not be a safe indexing operation
def third (xs : List α) (ok : xs.length > 2) : α := xs[2]  -- `xs.length > 2` is a proposition that is true or false, and `ok` must be evidence that it is true
-- otherwise, can use `?` to get an `Option`, where `some` if index in bounds and `none` otherwise
def thirdOption (xs : List α) : Option α := xs[2]?
#eval thirdOption woodlandCritters

-- `woodlandCritters [1]` is wrong since whitespace indicates function application on list of one number
