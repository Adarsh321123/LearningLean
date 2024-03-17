-- def main : IO Unit := IO.println "Hello, world!"
-- run using `lean --run Chapter2.lean`
-- invokes `main` (should have type `IO Unit` if does not take command-line arguments)
-- so `IO Unit` is type of program that either throws an exception or returns a value of type `Unit`
-- `IO.println` is a function from strings to `IO` actions that write given string to standard output

-- Functional Programming vs Effects
-- we have Lean language and compiler which does all theorem stuff
-- we also have run-time system (RTS) which implements basic effects and interacts with the user
-- so programs have no side effects

-- Combining IO Actions
def main : IO Unit := do  -- `do` is a sublang that allows these `IO` actions to be composed into a larger program
  -- `do` block is executed one line at a time
  let stdin ← IO.getStdin  -- value of expression is IO action that must be executed
  let stdout ← IO.getStdout

  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.dropRightWhile Char.isWhitespace  -- removes trailing newline and any other trailing whitespace

  stdout.putStrLn s!"Hello, {name}!"


-- Lean build tool is called Lake
-- can use `#eval` to evaluate expression and execute resulting action value
