/-!
# Interlude: Propositions, Proofs, and Indexing

A guided tour through the interlude that follows Chapter 2 of *Functional
Programming in Lean*
(<https://lean-lang.org/functional_programming_in_lean/Interlude___-Propositions___-Proofs___-and-Indexing/>).

Each part of the interlude is a `section` (or `namespace`) below. The book's
examples come first, followed by its exercises for you to solve.

Open this file in VS Code with the Lean 4 extension and put your cursor on any
`#eval`, `#check` or proof to see what Lean says in the *Lean Infoview* panel.

Examples that the book shows *failing* are kept as comments, so the file still
compiles.
-/

/-! ## Indexing lists

Square brackets look up an entry of a list, counting from 0.
-/
section Indexing

def woodlandCritters : List String := ["hedgehog", "deer", "snail"]

def hedgehog := woodlandCritters[0]
def deer := woodlandCritters[1]
def snail := woodlandCritters[2]

#eval snail    -- "snail"

-- Looking past the end of a list is a *compile-time* error, not a run-time
-- one. Lean tries to prove that the index is valid, `3 < woodlandCritters.length`,
-- and fails ("failed to prove index is valid"):
-- def oops := woodlandCritters[3]

end Indexing

/-! ## Propositions and Proofs

* A *proposition* is a statement that can be true or false, such as
  `1 + 1 = 2`.
* A *proof* is evidence that a proposition is true.

In Lean, **propositions are types, and proofs are values of those types**. A
false proposition is a type with no values. Propositions are themselves values
of type `Prop`, just as ordinary types are values of type `Type`.

`rfl` (*reflexivity*) is evidence that something equals itself. Lean accepts
it for `1 + 1 = 2` because both sides compute to the same value.
-/
section PropositionsAndProofs

#check 1 + 1 = 2     -- 1 + 1 = 2 : Prop
#check (Prop)        -- Prop : Type

-- The book first writes `def onePlusOneIsTwo : 1 + 1 = 2 := rfl`. Lean
-- accepts it, but suggests `theorem` instead of `def` for proofs.

-- `1 + 1` does not compute to `15`, so `rfl` is rejected
-- ("Not a definitional equality"):
-- theorem onePlusOneIsFifteen : 1 + 1 = 15 := rfl

-- A proposition can be given a name, like any other value.
def OnePlusOneIsTwo : Prop := 1 + 1 = 2

-- `theorem` is like `def`, but for proofs: Lean never needs to look inside a
-- proof once it has been checked, so it can check theorems in parallel.
theorem onePlusOneIsTwo : OnePlusOneIsTwo := rfl

end PropositionsAndProofs

/-! ## Tactics

Writing evidence by hand can be tedious. *Tactics* are small programs that
build the evidence for us. `by` switches to tactic mode, where the Infoview
shows the *goal* still to be proved (here `⊢ 1 + 1 = 2`).

* `decide` computes whether a proposition is true, when that can be done by
  running a program.
* `simp` rewrites the goal with known facts until it becomes trivial.
* `grind` is a more powerful automatic prover. It either proves the goal or
  fails.

Tactics keep working when definitions change, and they are what Lean uses to
prove that list indices are in bounds.
-/
namespace Tactics

theorem onePlusOneIsTwo : 1 + 1 = 2 := by decide

end Tactics

/-! ## Connectives

Propositions combine with logical *connectives*. For each, here is what counts
as evidence:

| Connective   | Lean    | Evidence                                           |
|--------------|---------|----------------------------------------------------|
| True         | `True`  | `True.intro`                                       |
| False        | `False` | none                                               |
| A and B      | `A ∧ B` | `And.intro a b`, from evidence for both            |
| A or B       | `A ∨ B` | `Or.inl a` or `Or.inr b`, from evidence for one    |
| A implies B  | `A → B` | a function turning evidence for A into one for B   |
| not A        | `¬A`    | a function from A to `False` (that is, `A → False`) |
-/
section Connectives

-- By hand ...
theorem addAndAppend' : 1 + 1 = 2 ∧ "Str".append "ing" = "String" :=
  And.intro rfl rfl

-- ... or with a tactic.
theorem addAndAppend : 1 + 1 = 2 ∧ "Str".append "ing" = "String" := by decide

-- Evidence for an implication is a function. Here it takes the evidence for
-- `A ∧ B` apart and uses the left half as evidence for `A ∨ B`.
theorem andImpliesOr : A ∧ B → A ∨ B :=
  fun andEvidence =>
    match andEvidence with
    | And.intro a _ => Or.inl a

theorem onePlusOneOrLessThan : 1 + 1 = 2 ∨ 3 < 5 := by decide
theorem notTwoEqualFive : ¬(1 + 1 = 5) := by decide
theorem trueIsTrue : True := by decide
theorem trueOrFalse : True ∨ False := by decide
theorem falseImpliesTrue : False → True := by decide

end Connectives

/-! ## Evidence as Arguments

`xs[2]` on an arbitrary list cannot be proved safe: Lean cannot know how long
`xs` is. This is rejected ("failed to prove index is valid", goal
`⊢ 2 < xs.length`):

```
def third (xs : List α) : α := xs[2]
```

The fix is to ask the *caller* for the evidence, as an extra argument. Lean
finds `ok` in scope and uses it to check the index.
-/
section EvidenceAsArguments

def third (xs : List α) (ok : xs.length > 2) : α := xs[2]

-- For a concrete list, `by decide` produces the evidence.
#eval third woodlandCritters (by decide)    -- "snail"

-- With too short a list, `decide` *disproves* the proposition
-- ("Tactic `decide` proved that the proposition ... is false"):
-- #eval third ["rabbit"] (by decide)

end EvidenceAsArguments

/-! ## Indexing Without Evidence

When we cannot (or do not want to) provide evidence:

* `xs[i]?` returns an `Option`: `some x` if `i` is in bounds, `none` if not.
* `xs[i]!` checks at run time, and crashes the program if `i` is out of bounds.
-/
section IndexingWithoutEvidence

def thirdOption (xs : List α) : Option α := xs[2]?

#eval thirdOption woodlandCritters    -- some "snail"
#eval thirdOption ["only", "two"]     -- none

#eval woodlandCritters[1]!            -- "deer"

end IndexingWithoutEvidence

/-! ## Messages You May Meet -/
section Messages

-- `simp` and `decide` do not look inside a `def`. `OnePlusOneIsTwo` was
-- defined with `def`, so both fail on it:
-- theorem onePlusOneIsStillTwo : OnePlusOneIsTwo := by simp
--   -- "`simp` made no progress"
-- theorem onePlusOneIsStillTwo : OnePlusOneIsTwo := by decide
--   -- "failed to synthesize Decidable OnePlusOneIsTwo"

-- Defining it with `abbrev` (see 1.3) fixes both:
abbrev OnePlusOneIsTwo' : Prop := 1 + 1 = 2

theorem onePlusOneIsStillTwo : OnePlusOneIsTwo' := by simp
theorem onePlusOneIsStillTwo' : OnePlusOneIsTwo' := by decide

-- When `xs[2]!` fails, it must still return *some* value of type `α`.
-- For an arbitrary `α`, Lean cannot know that one exists ("failed to
-- synthesize Inhabited α"). Chapter 3 explains how to fix this.
-- def unsafeThird (xs : List α) : α := xs[2]!

-- With a space before `[1]`, Lean reads this as applying `woodlandCritters`
-- to the list `[1]` ("Function expected"):
-- #eval woodlandCritters [1]

end Messages

/-! ## Exercises

Replace each `sorry` with your solution. -/
section Exercises

/-! Exercise 1: prove these with `rfl`. -/

theorem ex1a : 2 + 3 = 5 := sorry
theorem ex1b : 15 - 8 = 7 := sorry
theorem ex1c : "Hello, ".append "world" = "Hello, world" := sorry

-- What happens if you use `rfl` to prove `5 < 18`? Why? Uncomment to find out:
-- theorem ex1d : 5 < 18 := rfl

/-! Exercise 2: prove the same propositions with `by decide`. -/

theorem ex2a : 2 + 3 = 5 := sorry
theorem ex2b : 15 - 8 = 7 := sorry
theorem ex2c : "Hello, ".append "world" = "Hello, world" := sorry
theorem ex2d : 5 < 18 := sorry

/-- Exercise 3: look up the fifth entry of a list (index 4). The function
should take, as an argument, evidence that the lookup is safe. Fill in the
type of `ok` and the body. -/
def fifth (xs : List α) (ok : sorry) : α :=
  sorry

-- #eval fifth [1, 2, 3, 4, 5, 6] (by decide)    -- expected: 5

end Exercises
