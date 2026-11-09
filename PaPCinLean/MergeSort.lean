/-!
# Merge Sort: a certified sorting function

This is a Lean version of a "famous" example in ROCQ that appears in the
merge sort development in *Interactive Theorem Proving
and Program Development* (the "Coq'Art" book, Bertot and Castéran).

Merge sort cuts a list in two, sorts both halves, and merges the results. We
prove that its output is

1. **sorted**, and
2. a **permutation** of the input.

**Read `InsertSort.lean` first.** It proves the same two facts for insertion
sort, which is simpler: all its functions are structurally recursive. This
file adds the harder parts: functions that need well-founded recursion, and
proofs that follow them with `fun_induction`. It also defines permutations
differently. `InsertSort.lean` counts occurrences. Here a permutation is
built from the steps that rearrange a list.

The library already has sorted lists, permutations and a merge sort. Since
this file is for learning, we write our own versions from scratch. The last
section shows the same results using the library.

We sort lists of natural numbers with `≤`, so that the proofs can use
`omega` for the arithmetic. We keep Lean's own `List`, because rebuilding lists would teach us nothing new.

Open this file in VS Code with the Lean 4 extension and put your cursor inside
a proof to see the goal in the *Lean Infoview* panel.
-/

namespace MergeSort

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

/-- `LeHead a l` says that `a` is at most the first element of `l` (if `l` has
one). The proofs below use it to describe the head of a merged list. -/
def LeHead (a : Nat) : List Nat → Prop
  | [] => True
  | b :: _ => a ≤ b

/-- A list `a :: l` is sorted exactly when `a` is at most the head of `l` and
`l` is sorted. -/
theorem sorted_cons {a : Nat} {l : List Nat} :
    Sorted (a :: l) ↔ LeHead a l ∧ Sorted l := by
  constructor
  · intro h
    cases h with
    | one => exact ⟨trivial, .nil⟩
    | cons hle hs => exact ⟨hle, hs⟩
  · intro ⟨hle, hs⟩
    cases l with
    | nil => exact .one a
    | cons b l => exact .cons hle hs

/-! ### Permutations

Two lists are permutations of each other if one can be turned into the
other by

* adding the same element to the front of both (`skip`),
* swapping the first two elements (`swap`),
* doing several of these steps one after another (`trans`).
-/

inductive Perm : List Nat → List Nat → Prop
  | nil : Perm [] []
  | skip (x : Nat) {l l' : List Nat} : Perm l l' → Perm (x :: l) (x :: l')
  | swap (x y : Nat) (l : List Nat) : Perm (y :: x :: l) (x :: y :: l)
  | trans {l₁ l₂ l₃ : List Nat} : Perm l₁ l₂ → Perm l₂ l₃ → Perm l₁ l₃

namespace Perm

/-- Every list is a permutation of itself. -/
theorem refl : (l : List Nat) → Perm l l
  | [] => .nil
  | x :: l => .skip x (refl l)

/-- `Perm` is symmetric. -/
theorem symm {l l' : List Nat} (h : Perm l l') : Perm l' l := by
  induction h with
  | nil => exact .nil
  | skip x _ ih => exact .skip x ih
  | swap x y l => exact .swap y x l
  | trans _ _ ih₁ ih₂ => exact .trans ih₂ ih₁

/-- Adding the same list to the end of two permutations gives a
permutation. -/
theorem app_right {l₁ l₁' : List Nat} (h : Perm l₁ l₁') (l₂ : List Nat) :
    Perm (l₁ ++ l₂) (l₁' ++ l₂) := by
  induction h with
  | nil => exact refl l₂
  | skip x _ ih => exact .skip x ih
  | swap x y l => exact .swap x y (l ++ l₂)
  | trans _ _ ih₁ ih₂ => exact .trans ih₁ ih₂

/-- Adding the same list to the front of two permutations gives a
permutation. -/
theorem app_left (l₁ : List Nat) {l₂ l₂' : List Nat} (h : Perm l₂ l₂') :
    Perm (l₁ ++ l₂) (l₁ ++ l₂') := by
  induction l₁ with
  | nil => exact h
  | cons x l₁ ih => exact .skip x ih

/-- Permutations can be appended: if `l₁ ~ l₁'` and `l₂ ~ l₂'`, then
`l₁ ++ l₂ ~ l₁' ++ l₂'`. -/
theorem app {l₁ l₁' l₂ l₂' : List Nat} (h₁ : Perm l₁ l₁') (h₂ : Perm l₂ l₂') :
    Perm (l₁ ++ l₂) (l₁' ++ l₂') :=
  .trans (app_right h₁ l₂) (app_left l₁' h₂)

/-- An element can be moved from the front of a list to any position:
`a :: (l₁ ++ l₂) ~ l₁ ++ a :: l₂`. -/
theorem middle (a : Nat) : (l₁ l₂ : List Nat) → Perm (a :: (l₁ ++ l₂)) (l₁ ++ a :: l₂)
  | [], l₂ => refl (a :: l₂)
  | x :: l₁, l₂ =>
    -- `a :: x :: (l₁ ++ l₂) ~ x :: a :: (l₁ ++ l₂) ~ x :: (l₁ ++ a :: l₂)`
    .trans (.swap x a (l₁ ++ l₂)) (.skip x (middle a l₁ l₂))

end Perm

/-! ## The program

Merge sort has three parts:

* `split` cuts a list into two lists of about the same length,
* `merge` combines two sorted lists into one sorted list,
* `msort` splits the list, sorts both halves recursively, and merges them.

### Splitting

`split` deals the elements out like cards: the first to the left, the second
to the right, the third to the left, and so on. This keeps the two halves
within one element of each other in length, and it needs only one pass over
the list, without computing its length first.
-/

def split : List Nat → List Nat × List Nat
  | [] => ([], [])
  | [x] => ([x], [])
  | x :: y :: l =>
    let (l₁, l₂) := split l
    (x :: l₁, y :: l₂)

#eval split [1, 2, 3, 4, 5]    -- ([1, 3, 5], [2, 4])

/-- Neither half is longer than the original list. `msort` needs this to show
that its recursive calls are on shorter lists. -/
theorem split_length :
    (l : List Nat) → (split l).1.length ≤ l.length ∧ (split l).2.length ≤ l.length
  | [] => ⟨Nat.le_refl _, Nat.le_refl _⟩
  | [_] => ⟨Nat.le_refl _, Nat.zero_le _⟩
  | _ :: _ :: l => by
    have ih := split_length l
    simp only [split, List.length_cons]
    omega

/-- Splitting loses no elements: `l ~ l₁ ++ l₂`. -/
theorem split_perm : (l : List Nat) → Perm l ((split l).1 ++ (split l).2)
  | [] => .nil
  | [x] => Perm.refl [x]
  | x :: y :: l => by
    -- Goal: `x :: y :: l ~ x :: (l₁ ++ y :: l₂)`, where `(l₁, l₂) = split l`.
    show Perm (x :: y :: l) (x :: ((split l).1 ++ y :: (split l).2))
    exact .skip x (.trans (.skip y (split_perm l)) (Perm.middle y _ _))

/-! ### Merging

Each recursive call of `merge` makes *one* of the two lists shorter, but not
always the same one, so `merge` is not structurally recursive on either
argument. Lean still accepts the obvious definition: it finds a termination
measure by itself (here, that the pair of lists gets smaller in the
lexicographic order).
-/

def merge : List Nat → List Nat → List Nat
  | [], l₂ => l₂
  | l₁, [] => l₁
  | x :: l₁, y :: l₂ =>
    if x ≤ y then x :: merge l₁ (y :: l₂)
    else y :: merge (x :: l₁) l₂

#eval merge [1, 4, 6] [2, 3, 7]    -- [1, 2, 3, 4, 6, 7]

/-! ### Sorting

`msort` is not structurally recursive either: it calls itself on the two
halves made by `split`, which are not sub-terms of the input. Here we use
well-founded recursion and say why it terminates: `termination_by` names
the measure, the length of the list, and `decreasing_by` proves that each
recursive call is on a shorter list.

We split `l` rather than `x :: y :: l`. Then both halves have at least one
element, so for a list with two or more elements both recursive calls are
clearly on shorter lists.
-/

def msort : List Nat → List Nat
  | [] => []
  | [x] => [x]
  | x :: y :: l =>
    match _h : split l with
    | (l₁, l₂) => merge (msort (x :: l₁)) (msort (y :: l₂))
termination_by l => l.length
decreasing_by
  all_goals
    have := split_length l
    simp only [_h] at this
    simp only [List.length_cons]
    omega

#eval msort [5, 3, 8, 1, 9, 2, 7, 3]    -- [1, 2, 3, 3, 5, 7, 8, 9]

/-! ## Correctness of `merge`

### `merge` returns a sorted list

The key fact: if `a` is at most the heads of both lists, then it is at most
the head of their merge. The head of `merge l₁ l₂` is always the head of `l₁`
or the head of `l₂`.

`fun_induction merge l₁ l₂` does induction that follows the definition of
`merge`, with one case for each of its four branches.
-/

theorem leHead_merge {a : Nat} {l₁ l₂ : List Nat} :
    LeHead a l₁ → LeHead a l₂ → LeHead a (merge l₁ l₂) := by
  fun_induction merge l₁ l₂ <;> simp_all [LeHead]

theorem sorted_merge {l₁ l₂ : List Nat} :
    Sorted l₁ → Sorted l₂ → Sorted (merge l₁ l₂) := by
  fun_induction merge l₁ l₂ with
  | case1 l₂ => intro _ h₂; exact h₂
  | case2 l₁ _ => intro h₁ _; exact h₁
  | case3 x l₁ y l₂ hxy ih =>
    -- `x` comes first. It is at most the head of `l₁` (because `x :: l₁` is
    -- sorted) and at most `y` (because `x ≤ y`).
    intro h₁ h₂
    have ⟨hx, hl₁⟩ := sorted_cons.mp h₁
    exact sorted_cons.mpr ⟨leHead_merge hx hxy, ih hl₁ h₂⟩
  | case4 x l₁ y l₂ hxy ih =>
    -- `y` comes first. It is at most the head of `l₂` (because `y :: l₂` is
    -- sorted) and at most `x` (because `¬ x ≤ y`).
    intro h₁ h₂
    have ⟨hy, hl₂⟩ := sorted_cons.mp h₂
    have hyx : LeHead y (x :: l₁) := by simp only [LeHead]; omega
    exact sorted_cons.mpr ⟨leHead_merge hyx hy, ih h₁ hl₂⟩

/-! ### `merge` is a permutation of its inputs -/

theorem merge_perm (l₁ l₂ : List Nat) : Perm (l₁ ++ l₂) (merge l₁ l₂) := by
  fun_induction merge l₁ l₂ with
  | case1 l₂ => exact Perm.refl l₂
  | case2 l₁ _ => rw [List.append_nil]; exact Perm.refl l₁
  | case3 x l₁ y l₂ _ ih =>
    -- `(x :: l₁) ++ l₂` is `x :: (l₁ ++ l₂)`.
    exact .skip x ih
  | case4 x l₁ y l₂ _ ih =>
    -- Move `y` from the middle to the front, then use the induction hypothesis.
    exact .trans (Perm.middle y (x :: l₁) l₂).symm (.skip y ih)

/-! ## Correctness of `msort`

Both proofs use `fun_induction msort l`, which follows the definition of
`msort`. In the third case we get one induction hypothesis for each recursive
call, plus the equation `h : split l = (l₁, l₂)`.
-/

theorem sorted_msort (l : List Nat) : Sorted (msort l) := by
  fun_induction msort l with
  | case1 => exact .nil
  | case2 x => exact .one x
  | case3 x y l l₁ l₂ _ ih₁ ih₂ => exact sorted_merge ih₁ ih₂

theorem msort_perm (l : List Nat) : Perm l (msort l) := by
  fun_induction msort l with
  | case1 => exact .nil
  | case2 x => exact Perm.refl [x]
  | case3 x y l l₁ l₂ h ih₁ ih₂ =>
    -- First `x :: y :: l ~ (x :: l₁) ++ (y :: l₂)`, using `split_perm`:
    -- `x :: y :: l ~ x :: y :: (l₁ ++ l₂) ~ x :: (l₁ ++ y :: l₂)`.
    have hsplit : Perm l (l₁ ++ l₂) := by
      have := split_perm l
      rw [h] at this
      exact this
    have h₁ : Perm (x :: y :: l) ((x :: l₁) ++ (y :: l₂)) :=
      .skip x (.trans (.skip y hsplit) (Perm.middle y l₁ l₂))
    -- Then sort the two halves and merge them.
    exact .trans h₁ (.trans (Perm.app ih₁ ih₂) (merge_perm _ _))

/-! ## A certified sorting function

We can also state the specification of a program as its type: the function
returns a list *together with* a proof that it is correct. Then any caller
gets the proof along with the result. In Lean
we write this with a subtype `{ l' // P l' }`. -/

def sort (l : List Nat) : { l' : List Nat // Sorted l' ∧ Perm l l' } :=
  ⟨msort l, sorted_msort l, msort_perm l⟩

#eval (sort [3, 1, 2]).val    -- [1, 2, 3]

end MergeSort

/-! ## Using the library

The library has all of the pieces above:

| This file          | Library                                             |
|--------------------|-----------------------------------------------------|
| `MergeSort.Sorted` | `List.Pairwise` (a list is sorted when every pair `a, b` with `a` before `b` has `a ≤ b`) |
| `MergeSort.Perm`   | `List.Perm`, written `l₁ ~ l₂`                       |
| `MergeSort.merge`  | `List.merge`                                        |
| `MergeSort.msort`  | `List.mergeSort`                                    |
| `sorted_msort`     | `List.pairwise_mergeSort`                           |
| `msort_perm`       | `List.mergeSort_perm`                               |

The library functions work for any type `α`. They take the order as a
function `le : α → α → Bool`; by default it is `fun a b => a ≤ b`. The
sortedness theorem needs `le` to be transitive and total.

`List.Pairwise` relates *every* pair of elements, not just neighbours as our
`Sorted` does. For a transitive order the two definitions are equivalent.
-/

section Library

#eval [5, 3, 8, 1, 9, 2, 7, 3].mergeSort    -- [1, 2, 3, 3, 5, 7, 8, 9]

-- The library version of `sorted_msort`. The two arguments say that `≤` on
-- `Nat` is transitive and total.
example (l : List Nat) : (l.mergeSort (· ≤ ·)).Pairwise (· ≤ ·) := by
  have := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
    (fun a b c hab hbc => by simp at *; omega)
    (fun a b => by simp; omega)
    l
  simpa using this

-- The library version of `msort_perm`. The library states it the other way
-- round, `mergeSort l ~ l`, so we use `List.Perm.symm`.
example (l : List Nat) : l.Perm (l.mergeSort (· ≤ ·)) :=
  (List.mergeSort_perm l _).symm

-- The certified sort again, built from library parts only.
def librarySort (l : List Nat) :
    { l' : List Nat // l'.Pairwise (· ≤ ·) ∧ l.Perm l' } :=
  ⟨l.mergeSort (· ≤ ·),
   by
    have := List.pairwise_mergeSort (le := fun a b : Nat => decide (a ≤ b))
      (fun a b c hab hbc => by simp at *; omega)
      (fun a b => by simp; omega)
      l
    simpa using this,
   (List.mergeSort_perm l _).symm⟩

#eval (librarySort [3, 1, 2]).val    -- [1, 2, 3]

end Library
