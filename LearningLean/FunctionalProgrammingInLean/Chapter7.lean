-- overall:
-- a Monad is a way to encode values as well as sequential operations on those values (like a conveyor belt)
-- `IO` is a Monad that deals with reading and writing in a confined fashion, so it handles writing to a file and keeps the rest of
-- the program pure and without side effects
-- a Monad Transformer can combine two Monads, like one for error handling and one for IO
-- so `ReaderT` is a transformer that adds a layer to the `IO` monad so the program can access a `Config`
-- so `ConfigIO` combines `IO` with `ReaderT` transformer so we can do IO ops but pass configs around too
-- `showFileName` and `dirTree` perform tasks within the `ConfigIO` context so they can do IO ops and access shared configs

-- typical application has a core of testable functions without monads
-- then, there is an outer monad that encodes logic like mutable state, error handling, and logic
-- monad can be built from a collection of monad transformers

structure Config where
  useASCII : Bool := False
  currentPrefix : String := ""

def usage : String :=
  "Usage: doug [--ascii]
Options:
\t--ascii\tUse ASCII characters to display the directory structure"

def configFromArgs : List String → Option Config
  | [] => some {}  -- no command line argument provided, so both fields default in Config
  | ["--ascii"] => some {useASCII := true}
  | _ => none  -- for any other arguments, return none since we could not find a valid configuration

inductive Entry where
  | file : String → Entry
  | dir : String → Entry

def toEntry (path : System.FilePath) : IO (Option Entry) := do
  match path.components.getLast? with
  | none => pure (some (.dir ""))  -- path is root directory
  | some "." | some ".." => pure none  -- special navigation
  | some name =>
    pure (some (if (← path.isDir) then .dir name else .file name))  -- wrap in corresponding constructors

def Config.preFile (cfg : Config) :=
  if cfg.useASCII then "|--" else "├──"

def Config.preDir (cfg : Config) :=
  if cfg.useASCII then "|  " else "│  "

def Config.fileName (cfg : Config) (file : String) : String :=
  s!"{cfg.currentPrefix}{cfg.preFile} {file}"

def Config.dirName (cfg : Config) (dir : String) : String :=
  s!"{cfg.currentPrefix}{cfg.preFile} {dir}/"

def Config.inDirectory (cfg : Config) : Config :=
  {cfg with currentPrefix := cfg.preDir ++ " " ++ cfg.currentPrefix}  -- extends prefix with directory marker

-- old
-- def showFileName (cfg : Config) (file : String) : IO Unit := do
--   IO.println (cfg.fileName file)

-- def showDirName (cfg : Config) (dir : String) : IO Unit := do
--   IO.println (cfg.dirName dir)


-- old
-- -- manually passing a configuration is error-prone, so a reader effect ensures that the same config is passed to all recursive calls
-- -- we will create a version of `IO` that is also a reader of `Config`
-- def ConfigIO (α : Type) : Type :=
--   Config → IO α

-- new
-- manually passing a configuration is error-prone, so a reader effect ensures that the same config is passed to all recursive calls
-- we will create a version of `IO` that is also a reader of `Config`
abbrev ConfigIO (α : Type) : Type := ReaderT Config IO α

def read [Monad m] : ReaderT ρ m ρ :=
  fun env => pure env

-- old
-- instance : Monad ConfigIO where
--   pure x := fun _ => pure x
--   bind result next := fun cfg => do
--     let v ← result cfg
--     next v cfg

-- new
-- `ReaderT ρ m` is monad transformer that adds an environment of type `ρ` (config) to a computation of type `m` (another monad like `IO`)
instance [Monad m] : Monad (ReaderT ρ m) where  -- defining how `ReaderT` behaves as a monad, provided that `m` is also a monad
  -- `pure` takes a value `x` and wraps it into a monad
  pure x := fun _ => pure x   -- ignores environment (`_`) and returns `x` wrapped in monad `m`
  bind result next := fun env => do  -- takes monadic value `result`, applies function `next` to unwrapped result, and returns a new monadic value
    let v ← result env  -- environment passed to `result` to get `v`
    next v env  -- `v` passed to `next` along with `env` to get final result, ensures environment is available across chained operations
  -- `bind` has a pure operation since it only describes how the operations are composed, it doesn't actually do it
  -- actual side effects are managed by underlying monad `m` and only triggered when whole monad triggered by runtime system

-- running `ConfigIO` action involves transforming it into an `IO` action by providing a configuration
def ConfigIO.run (action : ConfigIO α) (cfg : Config) : IO α :=
  action cfg

def currentConfig : ConfigIO Config :=
  fun cfg => pure cfg  -- uses `pure` to return the value of `IO`

-- since entering a directory modifies the current configuration for the scope of the recursive call, we need to override a config
def locally (change : Config → Config) (action : ConfigIO α) : ConfigIO α :=
  fun cfg => action (change cfg)

-- old
-- ignores config arg
-- def runIO (action : IO α) : ConfigIO α :=
--   fun _ => action

-- no need for `runIO` anymore since `MonadLift` translates from monad `m` to monad `n`

-- old 2
-- -- take config arguments implicitly through `ConfigIO` Monad
-- def showFileName (file : String) : ConfigIO Unit := do
--   runIO (IO.println ((← currentConfig).fileName file))

-- def showDirName (dir : String) : ConfigIO Unit := do
--   runIO (IO.println ((← currentConfig).dirName dir))

-- new
-- take config arguments implicitly through `ConfigIO` Monad
def showFileName (file : String) : ConfigIO Unit := do
  IO.println s!"{(← read).currentPrefix} {file}"

def showDirName (dir : String) : ConfigIO Unit := do
  IO.println s!"{(← read).currentPrefix} {dir}/"

-- since `doList` does not base control-flow decisions on values returned by any action, we can use `Applicative` instead of `Monad`
def doList [Applicative f] : List α → (α → f Unit) → f Unit
  | [], _ => pure ()
  | x :: xs, action =>
    action x *>
    doList xs action

instance : MonadWithReader ρ (ReaderT ρ m) where
  withReader change action :=
    fun cfg => action (change cfg)

-- old
-- -- `dirTree` declared partial since Lean does not know that directory trees are finite (some systems alow for circular ones)
-- partial def dirTree (cfg : Config) (path : System.FilePath) : IO Unit := do
--   match ← toEntry path with
--   | none => pure ()
--   | some (.file name) => showFileName cfg name
--   | some (.dir name) =>
--     showDirName cfg name
--     let contents ← path.readDir
--     let newConfig := cfg.inDirectory
--     doList contents.toList fun d =>
--       dirTree newConfig d.path  -- recursively show contents in a new configuration where prefix is extended

-- old 2
-- -- `dirTree` declared partial since Lean does not know that directory trees are finite (some systems alow for circular ones)
-- partial def dirTree (path : System.FilePath) : ConfigIO Unit := do
--   match ← runIO (toEntry path) with
--   | none => pure ()
--   | some (.file name) => showFileName name
--   | some (.dir name) =>
--     showDirName name
--     let contents ← runIO path.readDir
--     locally (·.inDirectory)
--       (doList contents.toList fun d =>
--         dirTree d.path)  -- recursively show contents in a new configuration where prefix is extended

-- new
-- `dirTree` declared partial since Lean does not know that directory trees are finite (some systems alow for circular ones)
partial def dirTree (path : System.FilePath) : ConfigIO Unit := do
  match ← toEntry path with
  | none => pure ()
  | some (.file name) => showFileName name
  | some (.dir name) =>
    showDirName name
    let contents ← path.readDir
    locally (·.inDirectory)  -- `locally` means we can modify the config for just a small part of the program
      (doList contents.toList fun d =>
        dirTree d.path)  -- recursively show contents in a new configuration where prefix is extended

-- old
-- -- main processes command-line arguments and returns an exit code
-- def main (args : List String) : IO UInt32 := do
--   match configFromArgs args with  -- calls `configFromArgs` with `args`
--     | some config =>
--       dirTree config (← IO.currentDir)  -- `dirTree` shows the contents of a directory using a configuration
--       pure 0
--     | none =>
--       IO.eprintln s!"Didn't understand argument(s) {" ".separate args}\n"
--       IO.eprintln usage
--       pure 1

-- new
-- main processes command-line arguments and returns an exit code
-- this runs the directory listing ops within the `ConfigIO` context
def main (args : List String) : IO UInt32 := do
  match configFromArgs args with  -- calls `configFromArgs` with `args`
    | some config =>
      (dirTree (← IO.currentDir)).run config  -- `dirTree` shows the contents of a directory using a configuration
      pure 0
    | none =>
      IO.eprintln s!"Didn't understand argument(s) {" ".separate args}\n"
      IO.eprintln usage
      pure 1


-- monad transformer takes a monad and returns a new one
-- consist of (1) def of transformer, (2) `Monad` instance that assumes inner type is a monad, (3) operator to lift an action from inner to transformed monad
-- we added a reader effect by wrapping `IO α` in a function type, but Lean library can do that for any polymorphic type
-- def ReaderT (ρ : Type u) (m : Type u → Type v) (α : Type u) : Type (max u v) :=
--   ρ → m α

-- uses a state monad to count entries in a list
def count [Monad m] [MonadState Nat m] (p : α → m Bool) : List α → m Unit
  | [] => pure ()
  | x :: xs => do
    if ← p x then  -- `if not` can be replaced with `unless`
      modify (· + 1)
    count p xs

-- Using `do` to emulate imperative programming
def countLetters (str : String) : StateT LetterCounts (Except Err) Unit :=
  let rec loop (chars : List char) := do
    match chars with
    | [] => pure ()
    | c :: cs =>
      if c.isAlpha then
        if vowels.contains c then
          modify fun st => {st with vowels := st.vowels + 1}
        else if consonants.contains c then
          modify fun st => {st with consonants := st.consonants + 1}
        -- inserted automatically
        -- else  -- modified or non-English letter
        --   pure ()
      else throw (.notALetter c)
      loop cs
  loop str.toList


-- def List.forM [Monad M] : List α → (α → m PUnit) → m PUnit
--   | [], _ => pure ()
--   | x :: xs, action => do
--     action x
--     forM xs action

-- instance : ForM m (List α) α where
--   forM := List.forM

-- can stop early using `OptionT`
-- def countToThree (n : Nat) : IO Unit := do
--   let nums : AllLessThan := ⟨n⟩
--   for i in nums do
--     if i < 3 then break
--     IO.println i

def fourToEight : IO Unit := do
  for i in [4:9:2] do
    IO.println i   -- 4, 6, 8

-- can use local mutable variables since they are simulated by using `StateT`
def two : Nat := Id.run do  -- uses `Id` monad to use `do` without introducing side effects
  let mut x := 0
  x := x + 1
  x := x + 1
  return x

-- same as
def twoStateT : Nat :=
  let block : StateT Nat Id Nat := do
    modify (· + 1)
    modify (· + 1)
    return (← get)
  let (result, _finalState) := block 0  -- final state is ignored
  result

-- however can only use this local mutability in the context of the outer do block
-- so, if introduce another do block for a loop, cannot change the variable there


#eval two
