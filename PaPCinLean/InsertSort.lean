/-!
# Insertion Sort: a certified sorting function

This is a Lean version of a "famous" example in ROCQ that appears in the
insertion sort development in *Interactive Theorem Proving
and Program Development* (the "Coq'Art" book, Bertot and Castéran).

Insertion sort sorts a list by inserting its elements, one at a time, into a
list that is already sorted. We prove that the output is

1. **sorted**, and
2. a **permutation** of the input: it has the same elements, each the same
   number of times.

This is the simpler of the two sorting files. Read it before
`MergeSort.lean`, which sorts the same way but needs well-founded recursion.

The library already has sorted lists and permutations. Since this file is for
learning, we write our own versions from scratch. The last section links them
to the library.

We sort lists of natural numbers with `≤`, so that the proofs can use
`omega` for the arithmetic. We keep Lean's own `List`, because rebuilding lists would teach us nothing new.

Open this file in VS Code with the Lean 4 extension and put your cursor inside
a proof to see the goal in the *Lean Infoview* panel.
-/

namespace InsertSort

/-! ## Specification

### Sorted lists

We say when a list is sorted by comparing neighbours, with one constructor
for each of three cases:

* the empty list is sorted,
* a list with one element is sorted,
* `x :: y :: l` is sorted if `x ≤ y` and `y :: l` is sorted.
-/

inductive Sorted : List Nat → Prop
  | nil : Sorted []
  | one (x : Nat) : Sorted [x]
  | cons {x y : Nat} {l : List Nat} : x ≤ y → Sorted (y :: l) → Sorted (x :: y :: l)

example : Sorted [1, 2, 2, 5] :=
  .cons (by decide) (.cons (by decide) (.cons (by decide) (.one 5)))

/-! ### Permutations, by counting

A simple way to say that two lists are permutations of each other is by
counting: every number occurs the same number of times in both lists. With
this definition, most proofs about permutations come down to arithmetic on
the counts.

(`MergeSort.lean` instead defines permutations by the steps that rearrange a
list. That definition takes more work to use, but it needs no equality test
on the elements.)
-/

/-- `count z l` is the number of times `z` occurs in `l`. -/
def count (z : Nat) : List Nat → Nat
  | [] => 0
  | x :: l => if x = z then count z l + 1 else count z l

#eval count 2 [1, 2, 3, 2, 2]    -- 3

/-- `l` and `l'` have the same elements, each the same number of times. -/
def Equiv (l l' : List Nat) : Prop := ∀ z, count z l = count z l'

/-! `Equiv` is a function returning `Prop`, not an inductive type, so to prove
`Equiv l l'` we take any `z` (`intro z`) and prove that the two counts are
equal. Most of these proofs are arithmetic, which `simp` and `omega` handle.
-/

namespace Equiv

theorem refl (l : List Nat) : Equiv l l := fun _ => rfl

theorem symm {l l' : List Nat} (h : Equiv l l') : Equiv l' l :=
  fun z => (h z).symm

theorem trans {l₁ l₂ l₃ : List Nat} (h₁ : Equiv l₁ l₂) (h₂ : Equiv l₂ l₃) :
    Equiv l₁ l₃ :=
  fun z => (h₁ z).trans (h₂ z)

/-- Adding the same element to the front of both lists keeps them equivalent. -/
theorem cons (x : Nat) {l l' : List Nat} (h : Equiv l l') : Equiv (x :: l) (x :: l') := by
  intro z
  simp only [count, h z]

/-- Swapping the first two elements gives an equivalent list. -/
theorem swap (x y : Nat) (l : List Nat) : Equiv (x :: y :: l) (y :: x :: l) := by
  intro z
  simp only [count]
  split <;> split <;> rfl

end Equiv

/-! ## The program

### Inserting into a sorted list

`insert a l` walks along `l` and puts `a` just before the first element that
is at least `a`. If `l` is sorted, so is the result.
-/

def insert (a : Nat) : List Nat → List Nat
  | [] => [a]
  | x :: l => if a ≤ x then a :: x :: l else x :: insert a l

#eval insert 4 [1, 3, 5, 7]    -- [1, 3, 4, 5, 7]

/-! ### Sorting

`sort` inserts the elements of the list into the sorted tail, one at a time.
Unlike merge sort, both functions are structurally recursive: each recursive
call is on the tail of the list. -/

def sort : List Nat → List Nat
  | [] => []
  | x :: l => insert x (sort l)

#eval sort [5, 3, 8, 1, 9, 2, 7, 3]    -- [1, 2, 3, 3, 5, 7, 8, 9]

/-! ## Correctness of `insert`

### `insert` keeps a list sorted

The proof is by induction on the proof that `l` is sorted. Each case of
`Sorted` tells us how the list starts, which is what we need to unfold
`insert`.
`simp only [insert]` unfolds one step of `insert`, and `split` gives one goal
for each branch of the `if`.
-/

theorem sorted_insert (a : Nat) {l : List Nat} (h : Sorted l) : Sorted (insert a l) := by
  induction h with
  | nil => exact .one a
  | one x =>
    simp only [insert]
    by_cases hax : a ≤ x
    · -- The result is `[a, x]`.
      simp only [hax, ↓reduceIte]
      exact .cons hax (.one x)
    · -- The result is `[x, a]`.
      simp only [hax, ↓reduceIte]
      exact .cons (by omega) (.one a)
  | cons hxy hs ih =>
    -- The list is `x :: y :: l`, with `x ≤ y` and `y :: l` sorted.
    -- `ih : Sorted (insert a (y :: l))`.
    rename_i x y l
    simp only [insert]
    by_cases hax : a ≤ x
    · -- `a` goes at the front.
      simp only [hax, ↓reduceIte]
      exact .cons hax (.cons hxy hs)
    · -- The result is `x :: insert a (y :: l)`. To show it is sorted we need
      -- to know the head of `insert a (y :: l)`, so we unfold that `insert`
      -- too. Its head is either `a` or `y`, and both are at least `x`.
      simp only [hax, ↓reduceIte]
      simp only [insert] at ih ⊢
      by_cases hay : a ≤ y
      · simp only [hay, ↓reduceIte] at ih ⊢
        exact .cons (by omega) ih
      · simp only [hay, ↓reduceIte] at ih ⊢
        exact .cons hxy ih

/-! ### `insert` adds one element -/

theorem insert_equiv (a : Nat) (l : List Nat) : Equiv (a :: l) (insert a l) := by
  induction l with
  | nil => exact Equiv.refl [a]
  | cons x l ih =>
    simp only [insert]
    split
    · exact Equiv.refl _
    · -- `a :: x :: l ≈ x :: a :: l ≈ x :: insert a l`
      exact Equiv.trans (Equiv.swap a x l) (Equiv.cons x ih)

/-! ## Correctness of `sort`

Both proofs are by induction on the list. -/

theorem sorted_sort (l : List Nat) : Sorted (sort l) := by
  induction l with
  | nil => exact .nil
  | cons x l ih => exact sorted_insert x ih

theorem sort_equiv (l : List Nat) : Equiv l (sort l) := by
  induction l with
  | nil => exact Equiv.refl []
  | cons x l ih =>
    -- `x :: l ≈ x :: sort l ≈ insert x (sort l)`
    exact Equiv.trans (Equiv.cons x ih) (insert_equiv x (sort l))

/-! ## A certified sorting function

We can also state the specification of `sort` as its type: the function
returns a list *together with* a proof that it is correct. Then any caller
gets the proof along with the result. In Lean we write this with
a subtype `{ l' // P l' }`. -/

def certifiedSort (l : List Nat) : { l' : List Nat // Equiv l l' ∧ Sorted l' } :=
  ⟨sort l, sort_equiv l, sorted_sort l⟩

#eval (certifiedSort [3, 1, 2]).val    -- [1, 2, 3]

end InsertSort

/-! ## Using the library

Lean's core library has no insertion sort (Mathlib has one,
`List.insertionSort`), but it does have the specification:

| This file              | Library                                       |
|------------------------|-----------------------------------------------|
| `InsertSort.Sorted`    | `List.Pairwise (· ≤ ·)`                       |
| `InsertSort.count`     | `List.count`                                  |
| `InsertSort.Equiv`     | `List.Perm`, written `l₁ ~ l₂`                 |

`List.Pairwise R l` says that `R a b` holds for *every* pair of elements with
`a` before `b`, not just for neighbours as our `Sorted` does. For a transitive
order like `≤` the two say the same thing.

`List.perm_iff_count` says that `List.Perm` is exactly our `Equiv`: two lists
are permutations of each other when every element occurs the same number of
times in both.

Below we show that our `sort` also meets the library's specification.
-/

section Library

open InsertSort

/-- Our `count` is the library's `List.count`. -/
theorem InsertSort.count_eq (z : Nat) (l : List Nat) : count z l = l.count z := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [count, List.count_cons, ih, beq_iff_eq]
    split <;> simp

/-- Our `Equiv` is the library's `List.Perm`. -/
theorem InsertSort.equiv_iff_perm (l l' : List Nat) : Equiv l l' ↔ l.Perm l' := by
  rw [List.perm_iff_count]
  simp only [Equiv, count_eq]

/-- Our `Sorted` implies the library's `List.Pairwise (· ≤ ·)`. -/
theorem InsertSort.Sorted.pairwise {l : List Nat} (h : Sorted l) : l.Pairwise (· ≤ ·) := by
  induction h with
  | nil => exact .nil
  | one x => exact .cons (by simp) .nil
  | cons hxy _ ih =>
    -- `x ≤ y`, and `y` is at most every element after it, so `x` is too.
    refine .cons ?_ ih
    intro b hb
    cases hb with
    | head => exact hxy
    | tail _ hb => exact Nat.le_trans hxy (List.rel_of_pairwise_cons ih hb)

-- Our `sort`, with the library's specification.
example (l : List Nat) : (sort l).Pairwise (· ≤ ·) ∧ l.Perm (sort l) :=
  ⟨(sorted_sort l).pairwise, (equiv_iff_perm _ _).mp (sort_equiv l)⟩

end Library
