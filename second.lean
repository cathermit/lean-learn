-- run this in terminal lean --run second.lean

--def main : IO Unit := IO.println "Hello, World!"

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  stdout.putStrLn "who's there"
  let input ← stdin.getLine
  let name := input.dropRightWhile Char.isWhitespace

  stdout.putStrLn s!"{name} who?"
