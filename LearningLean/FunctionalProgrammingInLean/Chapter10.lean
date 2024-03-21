-- Tail Recursion
-- tail-call elimination in functional programming means that writing mutable loops
-- takes space on the stack, but rewriting them as recursive functions causes them to run quickly
-- tail call is call from on function to another that is compiled to an ordinary jump, replacing the current
-- stack frame rather than pushing a new one
-- tail-call elimination is process of eliminating this transformation

def NonTail.sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs  -- recursive call not in tail position since it is an argument to +

def Tail.sumHelper (soFar : Nat) : List Nat → Nat  -- function takes `soFar` and a list of natural numbers and then returns a natural number
  | [] => soFar
  | x :: xs => sumHelper (x + soFar) xs

def Tail.sum (xs : List Nat) : Nat :=
  Tail.sumHelper 0 xs

-- Tail.sum [1, 2, 3]
-- ===>
-- Tail.sumHelper 0 [1, 2, 3]
-- ===>
-- Tail.sumHelper (0 + 1) [2, 3]
-- ===>
-- Tail.sumHelper 1 [2, 3]
-- ===>
-- Tail.sumHelper (1 + 2) [3]
-- ===>
-- Tail.sumHelper 3 [3]
-- ===>
-- Tail.sumHelper (3 + 3) []
-- ===>
-- Tail.sumHelper 6 []
-- ===>
-- 6

-- nothing needs to be remembered to compute the final result
-- when base case is reached, we can return control directly to `Tail.sum`, since intermediate calls
-- of `Tail.sumHelper` return their results unmodified
-- so a single stack frame can be used for each call of `Tail.sumHelper`
-- this reuse is called tail-call elimination, so `Tail.sumHelper` is called a tail-recursive function

def NonTail.reverse : List α → List α
  | [] => []
  | x :: xs => reverse xs ++ [x]

def Tail.reverseHelper (soFar : List α) : List α → List α
  | [] => soFar
  | x :: xs => reverseHelper (x :: soFar) xs

def Tail.reverse (xs : List α) : List α :=
  Tail.reverseHelper [] xs


-- Tail.reverse [1, 2, 3]
-- ===>
-- Tail.reverseHelper [] [1, 2, 3]
-- ===>
-- Tail.reverseHelper [1] [2, 3]
-- ===>
-- Tail.reverseHelper [2, 1] [3]
-- ===>
-- Tail.reverseHelper [3, 2, 1] []
-- ===>
-- [3, 2, 1]

-- difficult to use accumulator-passing style if more than one recursive call at each step


-- Proving Equivalence
-- first attempt
-- we can prove that both versions of sum are equal by using function extensionality (same ouputs for same inputs)
-- theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
--   funext xs  -- `xs` is name for arbitrary argument (added as assumption)
--   -- now goal is `NonTail.sum xs = Tail.sum xs`
--   induction xs with
--   | nil => rfl  -- both functions return `0`
--   | cons y ys ih =>
--     simp [NonTail.sum, Tail.sum, Tail.sumHelper]
--     rw [ih]

-- theorem helper_add_sum_accum (xs : List Nat) (n : Nat) : n + Tail.sum xs = Tail.sumHelper n xs := by
--   induction xs with
--   | nil => rfl
--   | cons y ys ih =>
--     simp [Tail.sum, Tail.sumHelper]
--     -- now we are stuck since goal is `n + Tail.sumHelper y ys = Tail.sumHelper (y + n) ys`
--     -- but `ih` is `n + Tail.sum ys = Tail.sumHelper n ys`

-- second attempt
-- the reason these two versions are equal is that the accumulator increases by the same amount as
-- as the result of the recursion
-- so, ih needs to be applied to any accumulator value
theorem non_tail_sum_eq_helper_accum (xs : List Nat) : (n : Nat) → n + NonTail.sum xs = Tail.sumHelper n xs := by
  -- very important that `n` is after the colon, since then the goal is `∀ (n : Nat) ...`
  induction xs with
  | nil =>
    intro n  -- need to pick an arbitrary `n` to prove a `∀`
    rfl
  | cons y ys ih =>
    intro n
    simp [NonTail.sum, Tail.sumHelper]
    rw [← Nat.add_assoc]
    rw [Nat.add_comm y n]
    exact ih (n + y)

theorem non_tail_sum_eq_tail_sum : NonTail.sum = Tail.sum := by
  funext xs
  simp [Tail.sum]
  rw [← Nat.zero_add (NonTail.sum xs)]
  exact non_tail_sum_eq_helper_accum xs 0

-- pattern: find relationship between starting accumulator argument and final result (like accumulator of `n` means final sum added to `n`)
-- making this work with any starting accumulator is what is needed to get a strong ih


-- Arrays and Termination
-- need to prove that array index is in bounds and that array index that approaches size of array causes program to terminate
inductive IsThree : Nat → Prop where
  | isThree : IsThree 3

theorem three_is_three : IsThree 3 := by
  constructor

-- namespace Hidden
-- def arrayMapHelper (f : α → β) (arr : Array α) (soFar : Array β) (i : Nat) : Array β :=
--   if inBounds : i < arr.size then  -- giving a name adds it as a assumption
--     arrayMapHelper f arr (soFar.push (f arr[i])) (i + 1)
--   else soFar
-- termination_by arrayMapHelper _ arr _ i _ => arr.size - i  -- gives expression that shoiuld decrease on each call

-- def Array.map (f : α → β) (arr : Array α) : Array β :=
--   arrayMapHelper f arr Array.empty 0
-- end Hidden

-- structure Fin (n : Nat) where
--   val : Nat
--   isLt : LT.lt val n

-- namespace Hidden
-- def findHelper (arr : Array α) (p : α → Bool) (i : Nat) : Option (Fin arr.size × α) :=
--   if h : i < arr.size then
--     let x := arr[i]
--     if p x then
--       some (⟨i, h⟩, x)
--     else findHelper arr p (i + 1)
--   else none
-- termination_by findHelper arr p i => arr.size - i

-- def Array.find (arr : Array α) (p : α → Bool) : Option (Fin arr.size × α) :=
--   findHelper arr p 0
-- end Hidden


-- in-place algorithms are useful in Lean because of how it manages memory
-- instead of automatic memory management using tracing garbage collection, Lean uses reference counting
-- each object has field that tracks number of references to it
-- if counter reaches 0, the object is immediately deallocated
-- when asked to allocate a fresh object, Lean can recycle existing ones whose references counts are falling to 0
-- `Array.set` and `Array.swap` will mutate an array if its reference count is 1
-- `partial` means possible function may not terminate
-- try using `partial` at first to see if they return right answers and then remove `partial` and put `termination_by`
