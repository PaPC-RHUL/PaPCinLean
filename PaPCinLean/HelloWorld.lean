/-!
# Hello, World!

A guided tour through Chapter 2 of *Functional Programming in Lean*
(<https://lean-lang.org/functional_programming_in_lean/Hello___-World___/>).

Each section of the chapter is a `section` (or `namespace`) below. The book's
examples come first, followed by its exercises for you to solve.

Open this file in VS Code with the Lean 4 extension and put your cursor on any
`#eval` or `#check` line to see what Lean says in the *Lean Infoview* panel.

This chapter is about *programs*: things you compile and run, which talk to
the outside world. A file can only have one real entry point, so every `main`
below lives in its own namespace.

## Testing programs with `lean --run`

`#eval` runs IO actions, but with an empty standard input and no command-line
arguments. To test a program for real, run it with `lean --run`. There are two
ways to do it.

**1. A standalone file.** Copy the program (and anything it uses) into a file
of its own, with `main` outside any namespace, then run it:

```
$ lean --run Hello.lean
```

**2. A small wrapper around this file.** Build this file once, then write a
two-line file that imports it and picks the `main` you want:

```
$ lake build PaPCinLean.HelloWorld     # run again after every change here
```

```
-- Run.lean (anywhere in the project, for example in a scratch directory)
import PaPCinLean.HelloWorld
def main := RunningAProgram.HelloName.main
```

```
$ lake env lean --run Run.lean
```

`lake env` is needed so that `lean` can find this project's compiled modules.

In both cases:

* Words after the file name are passed to `main` as its arguments:
  `lean --run Cat.lean a.txt b.txt`.
* Standard input can come from a pipe instead of the keyboard:
  `echo "David" | lean --run HelloName.lean`.
* The exit code that `main` returns can be checked with `echo $?`.

Each program below has a comment showing how to test it.

## Failing examples

Examples that the book shows *failing* are kept as comments, so the file still
compiles.
-/

/-! ## 2.1 Running a Program

The simplest way to run a Lean program is `lean --run Hello.lean`, which runs
the file's `main`:

```
def main : IO Unit := IO.println "Hello, world!"
```

```
$ lean --run Hello.lean
Hello, world!
```
-/
namespace RunningAProgram

-- Test it: save the line below as `Hello.lean`, then `lean --run Hello.lean`.
-- Or, with the wrapper from the top of the file:
--   def main := RunningAProgram.main
def main : IO Unit := IO.println "Hello, world!"

/-! ### Anatomy of a greeting

* `main` has type `IO Unit`. There is no arrow, so `main` is *not a function*:
  it is a *description* of effects to carry out.
* `Unit` is the type with exactly one value, `()`. It carries no information,
  and plays the role of `void`.
* `IO α` is the type of actions that, when executed, may have side effects
  (or throw an exception) and then return a value of type `α`.
* `IO.println : String → IO Unit` turns a string into an action that prints it.
-/

#check (IO.println (α := String))    -- IO.println : String → IO Unit
#check main            -- main : IO Unit

/-! ### Functional programming vs effects

*Evaluating* an expression in Lean never has side effects. Effects happen when
the *run-time system* (RTS) *executes* the action that `main` evaluates to.

The book's analogy is a café. The cook (Lean) only prepares food from orders
(evaluates expressions to IO actions). The person at the counter (the RTS)
talks to the customers: it reads input and writes output, following the
cook's instructions.

One way to think of an `IO` action is as a function that takes "the whole
world" as an argument and returns a result together with a new world. Each
world token must be used exactly once, and the RTS supplies the first one.
-/

/-! ### Combining IO actions

`do` blocks run a sequence of steps in order:

* `let x ← action` *executes* `action` and names its result `x`.
* `let x := expr` is an ordinary local definition: nothing is executed.
* A bare `action` on its own line executes it and discards its `Unit` result.
-/
namespace HelloName

def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  stdout.putStrLn "How would you like to be addressed?"
  let input ← stdin.getLine
  let name := input.dropEndWhile Char.isWhitespace
  stdout.putStrLn s!"Hello, {name}!"

-- Test it: this program reads standard input, so `#eval` cannot really test
-- it. With `main` copied into `HelloName.lean`:
--   $ lean --run HelloName.lean
--   How would you like to be addressed?
--   David                                   <- typed by you
--   Hello, David!
-- Try typing a name with trailing spaces: they are removed.
-- The input can also come from a pipe (the question is still printed):
--   $ echo "David" | lean --run HelloName.lean
-- With the wrapper: `def main := RunningAProgram.HelloName.main`.

end HelloName

end RunningAProgram

/-! ## 2.2 Step By Step

We now execute `HelloName.main` one line at a time.
-/
section StepByStep

/-! ### Standard IO

`IO.getStdin` and `IO.getStdout` are themselves IO actions, not global
variables, so the streams they return can be swapped for others (for example,
in tests). Both return an `IO.FS.Stream`.
-/

#check IO.getStdin     -- IO.getStdin : BaseIO IO.FS.Stream
#check IO.getStdout    -- IO.getStdout : BaseIO IO.FS.Stream

/-! ### Asking a question

`stdout.putStrLn` is `IO.FS.Stream.putStrLn stdout` (dot notation), and
`stdin.getLine` returns the line *including* its final newline, for example
`"David\n"`. That is why the program removes trailing whitespace. Removing it
is a pure computation, so it uses `:=`, not `←`.
-/

#check (IO.FS.Stream.putStrLn)    -- IO.FS.Stream → String → IO Unit
#check (IO.FS.Stream.getLine)     -- IO.FS.Stream → IO String

#eval "Hello!!!".dropEndWhile (· == '!')                     -- Hello
#eval "Hello... ".dropEndWhile (fun c => not (c.isAlphanum))  -- Hello

/-! ### IO actions as values

Because evaluation and execution are separate, IO actions are ordinary values:
they can be passed to functions, returned, and stored in lists. `pure x` is
the action that does nothing and returns `x`.
-/

def twice (action : IO Unit) : IO Unit := do
  action
  action

#eval twice (IO.println "shy")    -- shy
                                  -- shy

def nTimes (action : IO Unit) : Nat → IO Unit
  | 0 => pure ()
  | n + 1 => do
    action
    nTimes action n

#eval nTimes (IO.println "Hello") 3    -- Hello (three times)

-- Building this list prints *nothing*: it only describes the printing.
def countdown : Nat → List (IO Unit)
  | 0 => [IO.println "Blast off!"]
  | n + 1 => IO.println s!"{n + 1}" :: countdown n

def from5 : List (IO Unit) := countdown 5

#eval from5.length    -- 6

def runActions : List (IO Unit) → IO Unit
  | [] => pure ()
  | act :: actions => do
    act
    runActions actions

-- Test it: a standalone `Countdown.lean` needs `countdown`, `from5` and
-- `runActions` too. With the wrapper: `def main := Countdown.main`.
--   $ lean --run Countdown.lean
--   5
--   4
--   3
--   2
--   1
--   Blast off!
namespace Countdown
def main : IO Unit := runActions from5
end Countdown

#eval Countdown.main    -- 5, 4, 3, 2, 1, Blast off! (one per line)

/-! ### Exercise

Step through the following program on paper. At each step, say whether an
expression is being *evaluated* or an IO action is being *executed*, and
write down any side effect. What does it print? Then uncomment the `#eval`
to check your prediction. -/

namespace Exercise
def main : IO Unit := do
  let englishGreeting := IO.println "Hello!"
  IO.println "Bonjour!"
  englishGreeting
end Exercise

-- #eval Exercise.main

-- Also check it as a real program, either by saving it as `Bonjour.lean` and
-- running `lean --run Bonjour.lean`, or with the wrapper
-- `def main := Exercise.main`. Is the output the same as with `#eval`?

end StepByStep

/-! ## 2.3 Starting a Project

Real programs are split over many files. Lean's build tool, *Lake*, manages
them. A Lake *package* contains *libraries* and *executables*.

```
$ lake new greeting      # create a package in a new directory `greeting/`
$ lake init              # or: turn the current directory into a package
$ lake build             # compile it
$ ./.lake/build/bin/greeting
Hello, world!
$ lake exe greeting      # build if needed, then run
Hello, world!
```

This project (`PaPCinLean`) is itself a Lake package: look at its
`lakefile.toml`.

### First steps

`lake new greeting` creates these files:

* `Main.lean`: where the compiler looks for `main`.
* `Greeting.lean` and `Greeting/Basic.lean`: the `Greeting` library.
* `lakefile.toml`: the build configuration.
* `lean-toolchain`: which version of Lean to use.

It also starts a git repository with a suitable `.gitignore`.

```
-- Greeting/Basic.lean
def hello := "world"
```

```
-- Greeting.lean
-- This module serves as the root of the `Greeting` library.
-- Import modules here that should be built as part of the library.
import Greeting.Basic
```

```
-- Main.lean
import Greeting

def main : IO Unit :=
  IO.println s!"Hello, {hello}!"
```

### Lakefiles

```
name = "greeting"
version = "0.1.0"
defaultTargets = ["greeting"]

[[lean_lib]]
name = "Greeting"

[[lean_exe]]
name = "greeting"
root = "Main"
```

By convention, packages and executables have lowercase names and libraries
have capitalised names. `defaultTargets` says what `lake build` builds when it
is given no target. A lakefile may also be written in Lean (`lakefile.lean`),
which allows more advanced configuration.

### Libraries and imports

A library is a hierarchy of *modules* (files). Dots in a module name follow
directories: `import Greeting.Smile` loads `Greeting/Smile.lean`.

Modules and namespaces are independent. A module is a unit of *compilation*;
a namespace is a unit of *naming*. One file can define names in many
namespaces, and one namespace can be spread over many files.

```
-- Greeting/Smile.lean
def Expression.happy : String := "a big smile"
```

```
-- Main.lean
import Greeting
import Greeting.Smile

open Expression

def main : IO Unit :=
  IO.println s!"Hello, {hello}, with {happy}!"
```

`open Expression` makes `Expression.happy` available as `happy`. To open only
some names, list them: `open Nat (toFloat)`.
-/
section StartingAProject

namespace Expression
def happy : String := "a big smile"
end Expression

open Expression in
#eval s!"Hello, world, with {happy}!"    -- "Hello, world, with a big smile!"

open Nat (toFloat) in
#eval toFloat 3    -- 3.000000

end StartingAProject

/-! ## 2.4 Worked Example: `cat`

We build `feline`, a simplified version of the Unix `cat` program. It copies
each file named on the command line to standard output, in order. The name `-`
stands for standard input, and with no arguments it reads standard input.

```
$ lake new feline exe    # the `exe` template has no library
```

```
name = "feline"
version = "0.1.0"
defaultTargets = ["feline"]

[[lean_exe]]
name = "feline"
root = "Main"
```
-/
namespace Feline

/-! ### Concatenating streams

Files may be large, or even infinite, so `feline` reads them in blocks of
20 KB instead of loading them whole. `USize` is an unsigned integer the size of
a machine pointer, like C's `size_t`.
-/

def bufsize : USize := 20 * 1024

/-! #### Streams

An `IO.FS.Stream` is a structure of IO actions, one per stream operation:

```
structure Stream where
  flush : IO Unit
  read : USize → IO ByteArray
  write : ByteArray → IO Unit
  getLine : IO String
  putStr : String → IO Unit
  isTty : BaseIO Bool
```

`dump` copies a stream to standard output, block by block, until a read
returns no bytes. The input could be infinite, so Lean cannot prove that
`dump` stops. The keyword `partial` lets us define it anyway.

Inside a `do` block, each branch of an `if` (or `match`) is its own `do` block.
The recursive call is the last thing `dump` does (a *tail call*), so the
compiled code is a loop and does not use up the stack.
-/

partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    let stdout ← IO.getStdout
    stdout.write buf
    dump stream

/-- Open a file as a stream. If the file is missing, report it on standard
error and return `none`. The file handle is closed automatically once nothing
refers to it any more. -/
def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
  let fileExists ← filename.pathExists
  if not fileExists then
    let stderr ← IO.getStderr
    stderr.putStrLn s!"File not found: {filename}"
    pure none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure (some (IO.FS.Stream.ofHandle handle))

/-! #### Handling input

`process` goes through the arguments and returns an *exit code*: 0 for
success, 1 if some file could not be opened. It recurses on a shorter list each
time, so it does not need `partial`. `System.FilePath` is a structure with a
single field, so `⟨filename⟩` builds one from a `String`.
-/

def process (exitCode : UInt32) (args : List String) : IO UInt32 := do
  match args with
  | [] => pure exitCode
  | "-" :: args =>
    let stdin ← IO.getStdin
    dump stdin
    process exitCode args
  | filename :: args =>
    let stream ← fileStream ⟨filename⟩
    match stream with
    | none =>
      process 1 args
    | some stream =>
      dump stream
      process exitCode args

/-! #### Main

`main` can have one of three types:

| type                          | arguments | exit code              | C analogue                   |
|-------------------------------|-----------|------------------------|------------------------------|
| `IO Unit`                     | no        | always 0               | `void main(void)`            |
| `IO UInt32`                   | no        | returned by `main`     | `int main(void)`             |
| `List String → IO UInt32`     | yes       | returned by `main`     | `int main(int argc, char **argv)` |
-/

def main (args : List String) : IO UInt32 :=
  match args with
  | [] => process 0 ["-"]
  | _ => process 0 args

/-! ### Meow!

```
$ echo "It works!" | lake exe feline
It works!

$ lake exe feline test1.txt test2.txt
It's time to find a warm spot
and curl up!

$ echo "and purr" | lake exe feline test1.txt - test2.txt
It's time to find a warm spot
and purr
and curl up!
```

You do not need a Lake package to try `feline`: `lean --run` passes the
words after the file name to `main`. Put `bufsize`, `dump`, `fileStream`,
`process` and `main` in `Feline.lean` (or use the wrapper with
`def main := Feline.main`, saved as `Cat.lean`), then:

```
$ echo "It's time to find a warm spot" > test1.txt
$ echo "and curl up!" > test2.txt
$ echo "and purr" | lean --run Feline.lean test1.txt - test2.txt
It's time to find a warm spot
and purr
and curl up!
$ lean --run Feline.lean test1.txt missing.txt
File not found: missing.txt
It's time to find a warm spot
$ echo $?
1
```

Things worth testing: no arguments at all (it reads standard input; type a
few lines and finish with Ctrl-D), `-` given twice, a missing file (the exit
code should be 1), and a large file. The error goes to standard error and the
rest to standard output, so their order on screen may vary.
-/

/-! ### Exercise

Extend `feline` so that, when given the argument `--help`, it prints a
description of the command-line options it accepts to standard output.
Replace the `sorry`s below, then copy your program into its own Lake package
(`lake new feline exe`) to try it, or test it with `lean --run`:

```
$ lean --run Feline.lean --help     # should print your help text
$ lean --run Feline.lean test1.txt  # should still work as before
```

With the wrapper, use `def main := Feline.V2.main`. Rebuild this file first
with `lake build PaPCinLean.HelloWorld`. -/

namespace V2

/-- The text printed by `feline --help`. -/
def helpText : String :=
  sorry

def main (args : List String) : IO UInt32 :=
  sorry

end V2

end Feline

/-! ## 2.5 Additional Conveniences -/
namespace Conveniences

open Feline (bufsize)

/-! ### Nested actions

`(← action)` inside an expression executes `action` and uses its result. Lean
moves the action out to the nearest enclosing `do` block and gives its result
a fresh name, so these definitions mean exactly the same as the ones in 2.4.
-/

partial def dump (stream : IO.FS.Stream) : IO Unit := do
  let buf ← stream.read bufsize
  if buf.isEmpty then
    pure ()
  else
    (← IO.getStdout).write buf
    dump stream

def fileStream (filename : System.FilePath) : IO (Option IO.FS.Stream) := do
  if not (← filename.pathExists) then
    (← IO.getStderr).putStrLn s!"File not found: {filename}"
    pure none
  else
    let handle ← IO.FS.Handle.mk filename IO.FS.Mode.read
    pure (some (IO.FS.Stream.ofHandle handle))

def getNumA : IO Nat := do
  (← IO.getStdout).putStrLn "A"
  pure 5

def getNumB : IO Nat := do
  (← IO.getStdout).putStrLn "B"
  pure 7

-- A nested action cannot be moved out of one branch of an `if` that is not
-- itself a step of the `do` block: that would run it even when the other
-- branch is taken. Lean rejects this with
-- "Nested action `← getNumB` must be nested inside a `do` expression":
-- def test : IO Unit := do
--   let a : Nat := if (← getNumA) == 5 then 0 else (← getNumB)
--   (← IO.getStdout).putStrLn s!"The answer is {a}"

-- If it were allowed, it would mean this, which *always* runs `getNumB`:
def test : IO Unit := do
  let x ← getNumA
  let y ← getNumB
  let a : Nat := if x == 5 then 0 else y
  (← IO.getStdout).putStrLn s!"The answer is {a}"

#eval test    -- A
              -- B
              -- The answer is 0

-- `lean --run` with the wrapper `def main := Conveniences.test` prints the
-- same thing: `test` reads no input, so `#eval` is already a faithful test.

/-! ### Flexible layouts for `do`

`do` blocks are normally laid out with one step per line, all at the same
indentation. Semicolons and braces may be used instead, but idiomatic Lean
rarely uses them. These three programs are the same.

Test it: run each one with `lean --run` (or the wrapper, with
`def main := Conveniences.V1.main`, then `V2`, then `V3`) and check that they
behave the same. Unlike `HelloName`, they use `trimAscii`, which removes
whitespace from *both* ends: try `echo "   David   " | lean --run V1.lean`.
-/

namespace V1
-- This version uses only whitespace-sensitive layout
def main : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout
  stdout.putStrLn "How would you like to be addressed?"
  let name := (← stdin.getLine).trimAscii
  stdout.putStrLn s!"Hello, {name}!"
end V1

namespace V2
-- This version is as explicit as possible
def main : IO Unit := do {
  let stdin ← IO.getStdin;
  let stdout ← IO.getStdout;
  stdout.putStrLn "How would you like to be addressed?";
  let name := (← stdin.getLine).trimAscii;
  stdout.putStrLn s!"Hello, {name}!"
}
end V2

namespace V3
-- This version uses a semicolon to put two actions on the same line
def main : IO Unit := do
  let stdin ← IO.getStdin; let stdout ← IO.getStdout
  stdout.putStrLn "How would you like to be addressed?"
  let name := (← stdin.getLine).trimAscii
  stdout.putStrLn s!"Hello, {name}!"
end V3

/-! ### Running IO actions with `#eval`

`#eval` *executes* IO actions, as we have been doing throughout this file. Two
things to keep in mind:

* Standard input is empty, so a program that reads it gets no input.
* Lean re-runs the file whenever it changes, so an `#eval` that writes or
  deletes files may run more often than you expect.
* `main` gets no command-line arguments, and its exit code is not shown.

So `#eval` is fine for quick checks, but anything that reads input, takes
arguments or touches files should be tested with `lean --run`.
-/

#eval runActions (countdown 3)    -- 3, 2, 1, Blast off! (one per line)

end Conveniences

/-! ## 2.6 Summary

### Evaluation vs execution

* Evaluating a Lean expression never has side effects.
* A value of type `IO α` is a *description* of effects. The run-time system
  executes it, producing an `α`. `pure x` has no effects and produces `x`.
* `main` has one of the types `IO Unit`, `IO UInt32` or
  `List String → IO UInt32`.

### `do` notation

* A step is an action to execute, `let x := e` (a plain definition), or
  `let x ← e` (execute `e` and name its result).
* Steps run in order. Each branch of an `if` or `match` step is its own `do`.
* `(← e)` is a nested action, moved to the nearest enclosing `do`.

### Compiling and running programs

* A single file with a `main`: `lean --run File.lean arg1 arg2 ...`. Use it to
  test programs that read input or take arguments, which `#eval` cannot do.
* Larger programs: `lake new` / `lake init` to create a package, `lake build`
  to compile it, and `lake exe NAME` to run it.

### Partiality

* Lean requires every function to terminate, so that every expression has a
  value. Recursion must be on smaller arguments (or come with a proof that it
  stops).
* `partial def` lifts this requirement, at a price: Lean will not evaluate a
  partial function while type checking, and we cannot prove things about it.
-/
