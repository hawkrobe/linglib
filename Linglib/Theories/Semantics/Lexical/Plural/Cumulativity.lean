import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Cumulative Predication



Formalizes Beck & Sauerland's cumulative operator `**`, which derives
cumulative truth conditions from transitive predicates applied to
pluralities.

## Distinction from CUM Reference

Link's CUM (`Mereology.CUM`) is a *property* of denotations: a predicate
P has cumulative reference iff P(x) ∧ P(y) → P(x ⊔ y). That is a
closure condition on extensions.

Beck & Sauerland's `**` is an *operator* that takes a two-place predicate
and returns a new predicate with cumulative truth conditions. The output
of `**` applied to a non-cumulative predicate is itself cumulative.

## Connection to Distributivity

DIST (in `Distributivity.lean`) universally distributes a one-place
predicate over atoms of a plurality:

  DIST(P)(x) = ∀a ≤ x. P(a)

`**` symmetrically distributes a two-place predicate over atoms of
*both* argument pluralities:

  **(R)(x, y) = [∀a ≤ x. ∃b ≤ y. R(a, b)] ∧ [∀b ≤ y. ∃a ≤ x. R(a, b)]

@cite{guerrini-2026} §4 uses `**` for cumulative kind predication:
"Elephants live in Africa and Asia" is true iff every elephant lives in
at least one of Africa/Asia, and each of Africa/Asia has at least one
elephant living in it.
-/

namespace Semantics.Lexical.Plural.Cumulativity

variable {A B : Type} [DecidableEq A] [DecidableEq B]

/--
The cumulative operator `**` (Beck & Sauerland 2000).

Given a two-place predicate R and two pluralities x : Finset A, y : Finset B:

  **(R)(x, y) = [∀a ∈ x. ∃b ∈ y. R(a, b)] ∧ [∀b ∈ y. ∃a ∈ x. R(a, b)]

Both argument pluralities must be "covered": every atom in x is
R-related to some atom in y, and vice versa.

Heterogeneous: A and B may be different types (e.g., Elephant × Continent).
-/
def cumulativeOp (R : A → B → Bool) (x : Finset A) (y : Finset B) : Bool :=
  decide (∀ a ∈ x, ∃ b ∈ y, R a b = true) &&
  decide (∀ b ∈ y, ∃ a ∈ x, R a b = true)

/--
Left coverage: every atom in x is R-related to some atom in y.
-/
def leftCoverage (R : A → B → Bool) (x : Finset A) (y : Finset B) : Bool :=
  decide (∀ a ∈ x, ∃ b ∈ y, R a b = true)

/--
Right coverage: every atom in y is R-related to some atom in x.
-/
def rightCoverage (R : A → B → Bool) (x : Finset A) (y : Finset B) : Bool :=
  decide (∀ b ∈ y, ∃ a ∈ x, R a b = true)

omit [DecidableEq A] [DecidableEq B] in
/-- `**` is the conjunction of left and right coverage. -/
theorem cumulativeOp_eq_coverages (R : A → B → Bool) (x : Finset A) (y : Finset B) :
    cumulativeOp R x y = (leftCoverage R x y && rightCoverage R x y) := rfl

omit [DecidableEq A] [DecidableEq B] in
/-- `**` entails DIST on the left argument: if `**(R)(x, y)` then every
    atom in x is R-related to *something* in y (left universality). -/
theorem cumulativeOp_left_universal (R : A → B → Bool) (x : Finset A) (y : Finset B)
    (h : cumulativeOp R x y = true) (a : A) (ha : a ∈ x) :
    ∃ b ∈ y, R a b = true := by
  simp only [cumulativeOp, Bool.and_eq_true, decide_eq_true_iff] at h
  exact h.1 a ha

omit [DecidableEq A] [DecidableEq B] in
/-- `**` entails DIST on the right argument: if `**(R)(x, y)` then every
    atom in y is R-related to *something* in x (right universality). -/
theorem cumulativeOp_right_universal (R : A → B → Bool) (x : Finset A) (y : Finset B)
    (h : cumulativeOp R x y = true) (b : B) (hb : b ∈ y) :
    ∃ a ∈ x, R a b = true := by
  simp only [cumulativeOp, Bool.and_eq_true, decide_eq_true_iff] at h
  exact h.2 b hb

omit [DecidableEq A] [DecidableEq B] in
/-- Left coverage with singleton right argument reduces to universal quantification.

    When the right plurality has exactly one element y, left coverage
    becomes: ∀a ∈ x. R(a, y).

    This is one half of @cite{johnston-2023}'s "number effect": with a
    singular object DP, the cumulative reading collapses to universal
    distribution, eliminating the pairing uncertainty that motivates
    over-informative elaboration. -/
theorem singleton_right_left_coverage (R : A → B → Bool) (x : Finset A) (y : B) :
    leftCoverage R x {y} = decide (∀ a ∈ x, R a y = true) := by
  simp only [leftCoverage, decide_eq_decide]
  constructor
  · intro h a ha
    obtain ⟨b, hb, hR⟩ := h a ha
    rw [Finset.mem_singleton.mp hb] at hR; exact hR
  · intro h a ha
    exact ⟨y, Finset.mem_singleton.mpr rfl, h a ha⟩

omit [DecidableEq A] [DecidableEq B] in
/-- Full `**` with singleton right argument and nonempty left argument.

    When `|Y| = 1` and `X` is nonempty, `**(R)(X, {y}) = ∀a ∈ X. R(a, y)`.
    Right coverage is trivially satisfied by any witness from X. -/
theorem singleton_right_cumulativeOp (R : A → B → Bool) (x : Finset A) (y : B)
    (hne : x.Nonempty) :
    cumulativeOp R x {y} = decide (∀ a ∈ x, R a y = true) := by
  rw [cumulativeOp_eq_coverages, singleton_right_left_coverage]
  cases hd : decide (∀ a ∈ x, R a y = true) with
  | false => simp
  | true =>
    simp only [Bool.true_and]
    rw [decide_eq_true_iff] at hd
    simp only [rightCoverage, decide_eq_true_iff, Finset.mem_singleton]
    intro b hb; rw [hb]
    obtain ⟨a, ha⟩ := hne
    exact ⟨a, ha, hd a ha⟩

-- Example: "Elephants live in Africa and Asia"

section ElephantExample

inductive Elephant where | dumbo | babar | tantor
  deriving DecidableEq, Repr

inductive Continent where | africa | asia
  deriving DecidableEq, Repr

instance : Fintype Elephant where
  elems := {.dumbo, .babar, .tantor}
  complete x := by cases x <;> simp

instance : Fintype Continent where
  elems := {.africa, .asia}
  complete x := by cases x <;> simp

def livesIn : Elephant → Continent → Bool
  | .dumbo,  .africa => true
  | .babar,  .africa => true
  | .tantor, .asia   => true
  | _,       _       => false

def allElephants : Finset Elephant := Finset.univ
def africaAndAsia : Finset Continent := Finset.univ

/-- "Elephants live in Africa and Asia" is true cumulatively:
    every elephant lives in at least one continent, and each continent
    has at least one elephant. -/
example : cumulativeOp livesIn allElephants africaAndAsia = true := by native_decide

/-- But Tantor doesn't live in Africa — the predicate doesn't hold
    for every (elephant, continent) pair. -/
example : livesIn .tantor .africa = false := rfl

end ElephantExample

end Semantics.Lexical.Plural.Cumulativity
