/-!
# Getting to Know Lean

A guided tour through Chapter 1 of *Functional Programming in Lean*
(<https://lean-lang.org/functional_programming_in_lean/Getting-to-Know-Lean/>).

Each section of the chapter is a `section` (or `namespace`) below. The book's
examples come first, followed by its exercises for you to solve. Worked
solutions are in `StartingSolved.lean`.

Open this file in VS Code with the Lean 4 extension and put your cursor on any
`#eval` or `#check` line to see what Lean says in the *Lean Infoview* panel.

Some definitions in the book are written several times, each version improving
on the last. Lean does not allow the same name to be defined twice, so later
versions live in their own namespaces (`V2`, `V3`, ...).

Examples that the book shows *failing* are kept as comments, so the file still
compiles.
-/

/-! ## 1.1 Evaluating Expressions

In functional programming, running a program means *evaluating an expression*
to a value, much like simplifying an expression in mathematics. `#eval` asks
Lean to evaluate an expression and show the result.
-/
section EvaluatingExpressions

#eval 1 + 2          -- 3
#eval 1 + 2 * 5      -- 11: the usual precedence rules apply

-- Function application is written with a *space*, not with parentheses and
-- commas. `String.append("Hello, ", "Lean!")` is a syntax error.
#eval String.append "Hello, " "Lean!"                        -- "Hello, Lean!"

-- Parentheses group nested applications.
#eval String.append "great " (String.append "oak " "tree")   -- "great oak tree"

-- `if ... then ... else ...` is an *expression* that has a value, like C's
-- ternary operator `c ? a : b`.
#eval String.append "it is " (if 1 > 2 then "yes" else "no") -- "it is no"

-- Leaving out an argument does not evaluate. Lean cannot display the resulting
-- function, so the following line is an error:
-- #eval String.append "it is "

/-! ### Exercises

What are the values of these expressions? Work them out by hand first, then
uncomment each line to check your answer with Lean. -/

-- #eval 42 + 19
-- #eval String.append "A" (String.append "B" "C")
-- #eval String.append (String.append "A" "B") "C"
-- #eval if 3 == 3 then 5 else 7
-- #eval if 3 == 4 then "equal" else "not equal"

end EvaluatingExpressions

/-! ## 1.2 Types

Every expression has a *type*. Types tell Lean (and us) what kind of value an
expression produces. The notation `(e : T)` says that `e` should have type `T`.
-/
section Types

#eval (1 + 2 : Nat)    -- 3

-- `Nat` holds the natural numbers 0, 1, 2, ... Subtraction cannot go below
-- zero, so it stops at 0.
#eval (1 - 2 : Nat)    -- 0

-- `Int` also has negative numbers.
#eval (1 - 2 : Int)    -- -1

-- `#check` shows an expression's type *without* evaluating it.
#check (1 - 2 : Int)   -- 1 - 2 : Int

-- Type errors are caught before the program runs. The following is rejected
-- because a `List String` is not a `String`:
-- #check String.append ["hello", " "] "world"

end Types

/-! ## 1.3 Functions and Definitions

`def` gives a name to a value. Functions are just definitions with arguments.
-/
section FunctionsAndDefinitions

def hello := "Hello"            -- the type `String` is inferred
def lean : String := "Lean"     -- or we can state it explicitly

#eval String.append hello (String.append " " lean)   -- "Hello Lean"

-- Arguments go before the `:`, each with its own type.
def add1 (n : Nat) : Nat := n + 1

#eval add1 7    -- 8

def maximum (n : Nat) (k : Nat) : Nat :=
  if n < k then k else n

def spaceBetween (before : String) (after : String) : String :=
  String.append before (String.append " " after)

-- Evaluation substitutes arguments, step by step:
--   maximum (5 + 8) (2 * 7)
--   ===> maximum 13 14
--   ===> if 13 < 14 then 14 else 13
--   ===> 14
#eval maximum (5 + 8) (2 * 7)   -- 14

-- `#check add1` shows the signature; wrapping the name in parentheses
-- shows the function's type instead.
#check add1         -- add1 (n : Nat) : Nat
#check (add1)       -- add1 : Nat → Nat
#check (maximum)    -- maximum : Nat → Nat → Nat

-- The arrow can also be written `->`. `example` checks a definition
-- without giving it a name.
example : Nat -> Nat := add1
example : Nat -> Nat -> Nat := maximum

-- `→` associates to the right: `Nat → Nat → Nat` means `Nat → (Nat → Nat)`.
-- A function with two arguments is a function that returns a function, so we
-- can supply fewer arguments than it takes (*partial application*).
#check maximum 3                 -- maximum 3 : Nat → Nat
#check spaceBetween "Hello "     -- spaceBetween "Hello " : String → String

/-! ### Defining types

Types are values too, so `def` can name them.
-/

def Str : Type := String
def aStr : Str := "This is a string."

def NaturalNumber : Type := Nat

-- Numeric literals are overloaded, and Lean does not look through `def` when
-- it searches for the overloading, so this fails:
-- def thirtyEight : NaturalNumber := 38
-- Giving the literal the type `Nat` fixes it.
def thirtyEight : NaturalNumber := (38 : Nat)

-- `abbrev` marks a definition to be unfolded freely, so literals just work.
abbrev N : Type := Nat
def thirtyNine : N := 39

/-! ### Exercises

Replace each `sorry` with your solution, then uncomment the checks below it. -/

/-- Exercise 1: put the first argument between the other two, so that
`joinStringsWith ", " "one" "and another"` evaluates to `"one, and another"`. -/
def joinStringsWith (sep : String) (before : String) (after : String) : String :=
  sorry

-- #eval joinStringsWith ", " "one" "and another"   -- expected: "one, and another"

-- Exercise 2: what is the type of `joinStringsWith ": "`? Answer here, then
-- uncomment the next line to check:
-- #check joinStringsWith ": "

/-- Exercise 3: the volume of a rectangular prism, given its height, width
and depth. Its type should be `Nat → Nat → Nat → Nat`. -/
def volume (height : Nat) (width : Nat) (depth : Nat) : Nat :=
  sorry

-- #eval volume 2 3 4    -- expected: 24

end FunctionsAndDefinitions

/-! ## 1.4 Structures

A `structure` groups several values (its *fields*) into a single value.
-/
section Structures

-- Decimal literals are `Float`s. A bare `0` is a `Nat` unless we ask otherwise.
#check 1.2            -- 1.2 : Float
#check -454.2123215   -- -454.2123215 : Float
#check 0.0            -- 0.0 : Float
#check 0              -- 0 : Nat
#check (0 : Float)    -- 0 : Float

-- `deriving Repr` lets `#eval` display values of the new type.
structure Point where
  x : Float
  y : Float
  deriving Repr

-- Values are built with `{ field := value, ... }` and fields are read with
-- dot notation.
def origin : Point := { x := 0.0, y := 0.0 }

#eval origin      -- { x := 0.000000, y := 0.000000 }
#eval origin.x    -- 0.000000
#eval origin.y    -- 0.000000

def addPoints (p1 : Point) (p2 : Point) : Point :=
  { x := p1.x + p2.x, y := p1.y + p2.y }

#eval addPoints { x := 1.5, y := 32 } { x := -8, y := 0.2 }
  -- { x := -6.500000, y := 32.200000 }

def distance (p1 : Point) (p2 : Point) : Float :=
  Float.sqrt (((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2.0))

#eval distance { x := 1.0, y := 2.0 } { x := 5.0, y := -1.0 }   -- 5.000000

-- Several structures may share field names.
structure Point3D where
  x : Float
  y : Float
  z : Float
  deriving Repr

def origin3D : Point3D := { x := 0.0, y := 0.0, z := 0.0 }

-- Without context, Lean cannot tell which structure `{ x := 0.0, y := 0.0 }`
-- belongs to, so `#check { x := 0.0, y := 0.0 }` is an error. Adding a type
-- annotation, either outside or inside the braces, solves it.
#check ({ x := 0.0, y := 0.0 } : Point)
#check { x := 0.0, y := 0.0 : Point }

/-! ### Updating structures

Values are immutable: an "update" builds a *new* value. The `with` syntax
copies every field except the ones listed.
-/

def zeroX (p : Point) : Point :=
  { p with x := 0 }

def fourAndThree : Point := { x := 4.3, y := 3.4 }

#eval fourAndThree          -- { x := 4.300000, y := 3.400000 }
#eval zeroX fourAndThree    -- { x := 0.000000, y := 3.400000 }
#eval fourAndThree          -- unchanged: { x := 4.300000, y := 3.400000 }

/-! ### Behind the scenes

A structure declaration creates a *constructor* (by default `mk`) and one
*accessor* function per field.
-/

#check Point.mk 1.5 2.8   -- { x := 1.5, y := 2.8 } : Point
#check (Point.mk)         -- Point.mk : Float → Float → Point
#check (Point.x)          -- Point.x : Point → Float
#check (Point.y)          -- Point.y : Point → Float
#eval Point.x origin      -- 0.000000

-- The constructor can be renamed with `name ::`.
namespace V2
structure Point where
  point ::
  x : Float
  y : Float
  deriving Repr

#check (Point.point)      -- Point.point : Float → Float → Point
end V2

-- `e.f` looks for a function `f` in the namespace of `e`'s type and passes
-- `e` as its first argument of that type.
#eval "one string".append " and another"    -- "one string and another"

def Point.modifyBoth (f : Float → Float) (p : Point) : Point :=
  { x := f p.x, y := f p.y }

#eval fourAndThree.modifyBoth Float.floor   -- { x := 4.000000, y := 3.000000 }

/-! ### Exercises -/

-- Exercise 1: define a structure `RectangularPrism` with a height, a width and
-- a depth, each a `Float`. Remember `deriving Repr`.

-- Exercise 2: define `RectangularPrism.volume`, which computes the volume of a
-- prism.

-- Exercise 3: define a structure `Segment` for a line segment, given by its
-- endpoints, and a function `Segment.length` that computes its length.
-- `Segment` should have at most two fields.

-- Exercise 4: which names does your `RectangularPrism` declaration introduce?
-- (Hint: `#check` them.)

-- Exercise 5: which names do the following `Hamster` and `Book` declarations
-- introduce, and what are their types?

structure Hamster where
  name : String
  fluffy : Bool

structure Book where
  makeBook ::
  title : String
  author : String
  price : Float

end Structures

/-! ## 1.5 Datatypes and Patterns

Structures combine values ("this *and* that"). *Inductive datatypes* offer a
choice ("this *or* that"). Each alternative is a *constructor*. In the standard
library:

```
inductive Bool where
  | false : Bool
  | true : Bool

inductive Nat where
  | zero : Nat
  | succ (n : Nat) : Nat
```

So `3` is really `Nat.succ (Nat.succ (Nat.succ Nat.zero))`. Pattern matching
with `match` looks at which constructor built a value.
-/
section DatatypesAndPatterns

def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ _ => false

#eval isZero 0    -- true
#eval isZero 5    -- false

-- A pattern can name the arguments of a constructor.
def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero => Nat.zero
  | Nat.succ k => k

#eval pred 5      -- 4
#eval pred 839    -- 838
#eval pred 0      -- 0

-- Structures can be matched too.
def depth (p : Point3D) : Float :=
  match p with
  | { x := _, y := _, z := d } => d

/-! ### Recursive functions

A recursive function on `Nat` calls itself on a *smaller* number, which
guarantees that it finishes (*structural recursion*).
-/

def even (n : Nat) : Bool :=
  match n with
  | Nat.zero => true
  | Nat.succ k => not (even k)

#eval even 10   -- true

-- Calling `evenLoops n` instead of `even k` would never terminate, and Lean
-- refuses it:
-- def evenLoops (n : Nat) : Bool :=
--   match n with
--   | Nat.zero => true
--   | Nat.succ k => not (evenLoops n)

def plus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => Nat.succ (plus n k')

def times (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => Nat.zero
  | Nat.succ k' => plus n (times n k')

def minus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => pred (minus n k')

#eval plus 3 4    -- 7
#eval times 3 4   -- 12
#eval minus 7 3   -- 4

-- Division recurses on `n - k`, which is not a direct sub-part of `n`, so Lean
-- cannot see on its own that it terminates. This is rejected:
-- def div (n : Nat) (k : Nat) : Nat :=
--   if n < k then 0 else Nat.succ (div (n - k) k)

end DatatypesAndPatterns

/-! ## 1.6 Polymorphism

Definitions can take *types* as arguments, which makes them work for any
type. By convention, type arguments are named with Greek letters such as `α`.
-/
section Polymorphism

structure PPoint (α : Type) where
  x : α
  y : α
  deriving Repr

def natOrigin : PPoint Nat := { x := Nat.zero, y := Nat.zero }

-- The type `α` is an ordinary, explicit argument here.
def replaceX (α : Type) (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }

#check (replaceX)                 -- (α : Type) → PPoint α → α → PPoint α
#check replaceX Nat               -- PPoint Nat → Nat → PPoint Nat
#check replaceX Nat natOrigin     -- Nat → PPoint Nat
#eval replaceX Nat natOrigin 5    -- { x := 5, y := 0 }

-- Types can depend on values: the result type here depends on `s`.
inductive Sign where
  | pos
  | neg
  deriving Repr

def posOrNegThree (s : Sign) : match s with | Sign.pos => Nat | Sign.neg => Int :=
  match s with
  | Sign.pos => (3 : Nat)
  | Sign.neg => (-3 : Int)

#eval posOrNegThree Sign.pos    -- 3
#eval posOrNegThree Sign.neg    -- -3

/-! ### Linked lists

The standard library defines lists like this:

```
inductive List (α : Type) where
  | nil : List α
  | cons : α → List α → List α
```

`[2, 3, 5, 7]` is shorthand for `List.cons 2 (List.cons 3 ...)`, and
`x :: xs` is shorthand for `List.cons x xs`.
-/

def primesUnder10 : List Nat := [2, 3, 5, 7]

def explicitPrimesUnder10 : List Nat :=
  List.cons 2 (List.cons 3 (List.cons 5 (List.cons 7 List.nil)))

-- Explicit type argument:
def length (α : Type) (xs : List α) : Nat :=
  match xs with
  | List.nil => Nat.zero
  | List.cons _ ys => Nat.succ (length α ys)

#eval length String ["Sourdough", "bread"]   -- 2

/-! ### Implicit arguments

Curly braces make an argument *implicit*: Lean works it out from the other
arguments, so we do not have to write it.
-/

namespace V2

def replaceX {α : Type} (point : PPoint α) (newX : α) : PPoint α :=
  { point with x := newX }

#eval replaceX natOrigin 5   -- { x := 5, y := 0 }

def length {α : Type} (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (length ys)

#eval length primesUnder10   -- 4

end V2

#eval primesUnder10.length       -- 4: the library's version
-- Implicit arguments can still be given explicitly, by name:
#check List.length (α := Int)    -- List Int → Nat

/-! ### More built-in datatypes -/

-- `Option α` is either `none` or `some x`: a value that might be missing.
-- Functions whose names end in `?` usually return an `Option`.
#eval primesUnder10.head?          -- some 2
#eval ([] : List Int).head?        -- none
#eval [].head? (α := Int)          -- none

-- `α × β` (a `Prod`) is a pair: an `α` *and* a `β`.
def fives : String × Int := ("five", 5)
def sevens : String × Int × Nat := ("VII", 7, 4 + 3)   -- = (String × (Int × Nat))

#eval fives.fst      -- "five"
#eval sevens.snd     -- (7, 7)

-- `α ⊕ β` (a `Sum`) is a choice: an `α` *or* a `β`.
-- Here `inl` holds dog names and `inr` holds cat names.
def PetName : Type := String ⊕ String

def animals : List PetName :=
  [Sum.inl "Spot", Sum.inr "Tiger", Sum.inl "Fifi", Sum.inl "Rex", Sum.inr "Floof"]

def howManyDogs (pets : List PetName) : Nat :=
  match pets with
  | [] => 0
  | Sum.inl _ :: morePets => howManyDogs morePets + 1
  | Sum.inr _ :: morePets => howManyDogs morePets

#eval howManyDogs animals    -- 3

-- `Unit` has exactly one value, `()`. It plays the role of `void`.
#check ()    -- () : Unit

inductive Firewood where
  | birch
  | pine
  | beech
  deriving Repr

def allFirewood : List Firewood := [Firewood.birch, Firewood.pine, Firewood.beech]

#eval allFirewood    -- [Firewood.birch, Firewood.pine, Firewood.beech]

/-! ### Exercises

Replace each `sorry` with your solution, then uncomment the checks below it. -/

/-- Exercise 1: the last entry of a list, if there is one. -/
def List.last? {α : Type} (xs : List α) : Option α :=
  sorry

-- #eval [1, 2, 3].last?          -- expected: some 3
-- #eval ([] : List Nat).last?    -- expected: none

/-- Exercise 2: the first entry of a list that satisfies `predicate`. -/
def List.findFirst? {α : Type} (xs : List α) (predicate : α → Bool) : Option α :=
  sorry

-- #eval [1, 2, 3, 4].findFirst? (fun n => n > 2)    -- expected: some 3

/-- Exercise 3: swap the two fields of a pair. -/
def Prod.switch {α β : Type} (pair : α × β) : β × α :=
  sorry

-- #eval (1, "one").switch    -- expected: ("one", 1)

-- Exercise 4: rewrite the `PetName` example with a custom datatype, and a
-- version of `howManyDogs` for it. How does it compare to the `Sum` version?

/-- Exercise 5: pair up two lists, stopping at the end of the shorter one. -/
def zip {α β : Type} (xs : List α) (ys : List β) : List (α × β) :=
  sorry

-- #eval zip [1, 2, 3] ["one", "two"]    -- expected: [(1, "one"), (2, "two")]

/-- Exercise 6: the first `n` entries of a list (or all of them, if there are
fewer). -/
def take {α : Type} (n : Nat) (xs : List α) : List α :=
  sorry

-- #eval take 3 ["bolete", "oyster"]    -- expected: ["bolete", "oyster"]
-- #eval take 1 ["bolete", "oyster"]    -- expected: ["bolete"]

/-- Exercise 7: using the analogy between types and arithmetic, write a
function with this type. Which rule of arithmetic does it correspond to? -/
def distribute {α β γ : Type} (x : α × (β ⊕ γ)) : (α × β) ⊕ (α × γ) :=
  sorry

/-- Exercise 8: and this one? (Hint: what is `Bool` in this analogy?) -/
def boolTimes {α : Type} (x : Bool × α) : α ⊕ α :=
  sorry

end Polymorphism

/-! ## 1.7 Characters, Strings and Slices

`Char` literals use single quotes, `String` literals double quotes. `++`
appends strings (and lists).
-/
section Strings

#eval "Hello, " ++ "world"       -- "Hello, world"
#eval String.push "Hello" '!'    -- "Hello!"
#eval "Hello".push '!'           -- "Hello!"

-- Operations like `drop` return a *slice*: a view into the original string,
-- without copying it. `copy` turns a slice back into a `String`.
#eval (("small tortoiseshell".drop 6).dropEnd 5).copy    -- "tortoise"

-- `dropWhile`/`dropEndWhile` take a *pattern*: a character, a string or a
-- predicate on characters.
#eval "red admiral".dropEndWhile 'l'                      -- red admira
#eval "the the butterfly".dropWhile "the "                -- butterfly
#eval ("a gray grayling".drop 2).dropWhile "gray "        -- grayling
#eval ("red admiral".dropEndWhile Char.isAlpha).copy      -- "red "

end Strings

/-! ## 1.8 Additional Conveniences

Shorter ways of writing what we have already seen.
-/
namespace Conveniences

/-! ### Automatic implicit parameters

Unbound lowercase single letters (and Greek letters) in a signature become
implicit type arguments automatically, so `{α : Type}` can be left out.
-/
def length (xs : List α) : Nat :=
  match xs with
  | [] => 0
  | _ :: ys => Nat.succ (length ys)

/-! ### Pattern-matching definitions

When a function immediately matches on its arguments, the patterns can be
written directly after the type.
-/
namespace V2
def length : List α → Nat
  | [] => 0
  | _ :: ys => Nat.succ (length ys)
end V2

def drop : Nat → List α → List α
  | Nat.zero, xs => xs
  | _, [] => []
  | Nat.succ n, _ :: xs => drop n xs

def fromOption (default : α) : Option α → α
  | none => default
  | some x => x

#eval (some "salmonberry").getD ""    -- "salmonberry" (the library's version)
#eval none.getD ""                    -- ""

/-! ### Local definitions

`let` names an intermediate value. Here it avoids calling `unzip xys` twice.
-/
def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped : List α × List β := unzip xys
    (x :: unzipped.fst, y :: unzipped.snd)

-- `let` can also take a structure apart with a pattern.
namespace V2
def unzip : List (α × β) → List α × List β
  | [] => ([], [])
  | (x, y) :: xys =>
    let (xs, ys) : List α × List β := unzip xys
    (x :: xs, y :: ys)
end V2

#eval unzip [(1, 'a'), (2, 'b')]    -- ([1, 2], ['a', 'b'])

-- `let rec` defines a local recursive helper.
def reverse (xs : List α) : List α :=
  let rec helper : List α → List α → List α
    | [], soFar => soFar
    | y :: ys, soFar => helper ys (y :: soFar)
  helper xs []

#eval reverse [1, 2, 3]    -- [3, 2, 1]

/-! ### Type inference

Lean can often infer types, but writing them down for top-level definitions
makes code easier to read and error messages easier to understand.
-/
namespace V3
def unzip (pairs : List (α × β)) :=    -- return type inferred
  match pairs with
  | [] => ([], [])
  | (x, y) :: xys =>
    let unzipped := unzip xys          -- type of `unzipped` inferred
    (x :: unzipped.fst, y :: unzipped.snd)
end V3

#check 14            -- 14 : Nat
#check (14 : Int)    -- 14 : Int

def id (x : α) : α := x

/-! ### Simultaneous matching

`match` can inspect several values at once, separated by commas.
-/
def sameLength (xs : List α) (ys : List β) : Bool :=
  match xs, ys with
  | [], [] => true
  | _ :: xs', _ :: ys' => sameLength xs' ys'
  | _, _ => false

#eval sameLength [1, 2] ["a", "b"]    -- true

/-! ### Natural number patterns

`n + 1` can be used as a pattern instead of `Nat.succ n`.
-/
def even : Nat → Bool
  | 0 => true
  | n + 1 => not (even n)

def halve : Nat → Nat
  | 0 => 0
  | 1 => 0
  | n + 2 => halve n + 1

#eval halve 9    -- 4

/-! ### Anonymous functions

`fun x => e` is a function without a name. `·` is an even shorter notation:
`(· + 1)` means `fun x => x + 1`.
-/
#check fun x => x + 1             -- fun x => x + 1 : Nat → Nat
#check fun (x : Int) => x + 1     -- fun x => x + 1 : Int → Int
#check fun {α} (x : α) => x       -- fun {α} x => x : {α : Sort u_1} → α → α

-- `fun` can pattern-match directly.
#check fun
  | 0 => none
  | n + 1 => some n               -- Nat → Option Nat

def double : Nat → Nat := fun
  | 0 => 0
  | k + 1 => double k + 2

#eval (fun x => x + x) 5    -- 10
#eval (· * 2) 5             -- 10
#eval (· , ·) 1 2           -- (1, 2)

/-! ### Namespaces

Names can be grouped into namespaces. A function in a type's namespace can be
used with dot notation.
-/
-- We are inside `namespace Conveniences`, so `_root_` is needed to put the
-- definition in the real `Nat` namespace rather than `Conveniences.Nat`.
def _root_.Nat.double (x : Nat) : Nat := x + x

#eval (4 : Nat).double    -- 8

namespace NewNamespace
def triple (x : Nat) : Nat := 3 * x
def quadruple (x : Nat) : Nat := 2 * x + 2 * x
end NewNamespace

#check NewNamespace.triple       -- Conveniences.NewNamespace.triple (x : Nat) : Nat

-- `open` makes a namespace's contents available without the prefix.
def timesTwelve (x : Nat) :=
  open NewNamespace in
  quadruple (triple x)

open NewNamespace in
#check quadruple

/-! ### `if let`

When we only care about one constructor, `if let` is shorter than `match`.
-/
inductive Inline : Type where
  | lineBreak
  | string : String → Inline
  | emph : Inline → Inline
  | strong : Inline → Inline

def Inline.string? (inline : Inline) : Option String :=
  if let Inline.string s := inline then
    some s
  else
    none

/-! ### Positional structure arguments

`⟨1, 2⟩` builds a structure from its fields in order, when the type is known.
-/
#eval (⟨1, 2⟩ : Point)    -- { x := 1.000000, y := 2.000000 }

/-! ### String interpolation

`s!"..."` evaluates the expressions in braces and inserts them into the string.
-/
#eval s!"three fives is {NewNamespace.triple 5}"    -- "three fives is 15"

end Conveniences

/-! ## 1.9 Summary

* Programs are expressions, and running a program means evaluating it.
* Every expression has a type, checked before the program runs.
* `def` names values and functions; `structure` groups values together;
  `inductive` describes a choice between constructors.
* `match` takes values apart by pattern; recursion must be on smaller values.
* Definitions can be polymorphic, with implicit type arguments in `{...}`.
-/
