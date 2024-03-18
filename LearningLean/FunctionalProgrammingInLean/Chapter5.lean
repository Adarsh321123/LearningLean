-- can use optional indexing notation to get first element
def first (xs : List α) : Option α :=
  xs[0]?

def firstThird (xs : List α) : Option (α × α) :=
  match xs[0]? with
  | none => none
  | some first =>
    match xs[2]? with
    | none => none
    | some third =>
      some (first, third)

def andThen (opt : Option α) (next : α → Option β) : Option β :=
  match opt with
  | none => none
  | some x => next x

def firstThirdSimple (xs : List α) : Option (α × α) :=
  andThen xs[0]? fun first =>
  andThen xs[2]? fun third =>
  some (first, third)

-- pure func langs like Lean have no eror handling
-- can make a datatype that is either error or result
-- and then have functions return this datatype
namespace Hidden
inductive Except (ε : Type) (α : Type) where
  -- `ε` is type of errors that func can produce
  | error : ε → Except ε α
  | ok : α → Except ε α
deriving BEq, Hashable, Repr

def get (xs : List α) (i : Nat) : Except String α :=
  match xs[i]? with
  | none => Except.error s!"Index {i} not found (maximum is {xs.length - 1})"
  | some x => Except.ok x
end Hidden

-- each monad encodes a side effect
-- so Option represents programs that can fail by returning none
-- Except represents programs that throw exceptions


-- Monad Type Class
namespace Hidden
class Monad (m : Type → Type) where  -- simplified
  pure : α → m α
  bind : m α → (α → m β) → m β

instance : Monad Option where
  pure x := some x
  bind opt next :=
    match opt with
    | none => none
    | some x => next x

-- uses a Monad to sequence and combine the results of applying a function
-- def mapM [Monad m] (f : α → m β) : List α → m (List β)
--   | [] => pure []
--   | x :: xs =>
--     f x >>= fun hd =>
--     mapM f xs >>= fun tl =>
--     pure (hd :: tl)

-- `State σ α` represents programs that make use of mutable variable of type `σ`
-- and return a value of type `α`

-- instance : Monad (State σ) where
--   pure x := fun s => (s, x)
--   bind first next :=
--     fun s =>
--       let (s', x) := first s
--       next x s'

-- sometimes, will use a monad for flexibility but not for side effects
def Id (t : Type) : Type := t

-- instance : Monad Id where
--   pure x := x
--   bind x f := f x
end Hidden

-- Example: Arithmetic in Monads
inductive Expr (op : Type) where
  | const : Int → Expr op
  | prim : op → Expr op → Expr op → Expr op

inductive Arith where
  | plus
  | minus
  | times
  | div

open Expr in
open Arith in
def twoPlusThree : Expr Arith :=
  prim plus (const 2) (const 3)

-- need to handle division by zero
def evaluateOption : Expr Arith → Option Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateOption e1 >>= fun v1 =>  -- `>>=` is bind operation
    evaluateOption e2 >>= fun v2 =>
    match p with
    | Arith.plus => pure (v1 + v2)
    | Arith.minus => pure (v1 - v2)
    | Arith.times => pure (v1 * v2)
    | Arith.div => if v2 == 0 then none else pure (v1 / v2)


def applyDivOption (x : Int) (y : Int) : Option Int :=
    if y == 0 then
      none
    else pure (x / y)

def applyDivExcept (x : Int) (y : Int) : Except String Int :=
    if y == 0 then
      Except.error s!"Tried to divide {x} by zero"
    else pure (x / y)

def applyPrim [Monad m] (applyDiv : Int → Int → m Int) : Arith → Int → Int → m Int
  | Arith.plus, x, y => pure (x + y)
  | Arith.minus, x, y => pure (x - y)
  | Arith.times, x, y => pure (x * y)
  | Arith.div, x, y => applyDiv x y

def evaluateM [Monad m] (applyDiv : Int → Int → m Int): Expr Arith → m Int
  | Expr.const i => pure i
  | Expr.prim p e1 e2 =>
    evaluateM applyDiv e1 >>= fun v1 =>
    evaluateM applyDiv e2 >>= fun v2 =>
    applyPrim applyDiv p v1 v2


-- do-Notation
-- first translation is turning `do E` to `E`
-- second is turning `do let x ← E1` to `E1 >>= fun x =>`
-- also `do E1` with a expression after turns to `E1 >>= fun () =>`
-- also `do let x := E1` turns to `let x := E1`


-- IO Monad tracks state and errors at the same time
-- collection of errors given by IO.Error
-- each IO action receives the world and returns another one, paired with an error or a result

-- or patterns
inductive Weekday where
  | monday
  | tuesday
  | wednesday
  | thursday
  | friday
  | saturday
  | sunday
  deriving Repr

def Weekday.isWeekend : Weekday → Bool
  | .saturday | .sunday => true
  | _ => false
