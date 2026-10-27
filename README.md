# PaPCinLean

A small Lean 4 project that follows the chapter
[Getting to Know Lean](https://lean-lang.org/functional_programming_in_lean/Getting-to-Know-Lean/)
from *Functional Programming in Lean*.

- `PaPCinLean/Starting.lean`: the chapter's examples, with comments, and its exercises left for you
  to solve (replace each `sorry`, then uncomment the checks below it).
- `PaPCinLean/StartingSolved.lean`: the same file with worked solutions to the exercises. (Available under request only!)
- `Main.lean`: a tiny executable that uses the library.

```sh
lake build            # check both files (Starting.lean warns about each unsolved `sorry`)
lake exe papcinlean   # run the executable
```

Open `PaPCinLean/Starting.lean` in VS Code with the Lean 4 extension and put the
cursor on an `#eval` or `#check` line to see its result in the Infoview.
