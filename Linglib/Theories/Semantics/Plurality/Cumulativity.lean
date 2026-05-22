import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Cumulative Predication
@cite{krifka-1989} @cite{sternefeld-1998} @cite{beck-sauerland-2000}

Formalises the cumulative operator `**`. The operator's lineage:

- **@cite{krifka-1989}**: original closure-form definition (smallest
  relation closed under `⟨a,b⟩+⟨c,d⟩ → ⟨a∪c, b∪d⟩`).
- **@cite{sternefeld-1998}**: extension to the n-ary case (paper §3.1
  defines `***` for three-place relations) — formalised in
  `Studies/Sternefeld1998.lean` (just the binary
  closure form so far).
- **@cite{beck-sauerland-2000}**: the bidirectional-coverage
  reformulation `(∀a∈x. ∃b∈y. R(a,b)) ∧ (∀b∈y. ∃a∈x. R(a,b))`
  that this file uses.

The two formulations are equivalent on Quine-innovation domains; the
forward direction `closure → coverage` is proven in
`Studies/Sternefeld1998.lean::sternefeldStarStar_implies_cumulative`.

## Distinction from CUM Reference

Link's CUM (`Mereology.CUM`) is a *property* of denotations: a predicate
P has cumulative reference iff P(x) ∧ P(y) → P(x ⊔ y). That is a
closure condition on extensions.

The `**` operator here takes a two-place predicate and returns a new
predicate with cumulative truth conditions. The output of `**` applied
to a non-cumulative predicate is itself cumulative.

## Consumers

- @cite{guerrini-2026} §4 uses `**` for cumulative kind predication:
  "Elephants live in Africa and Asia" is true iff every elephant lives
  in at least one of Africa/Asia, and each of Africa/Asia has at least
  one elephant living in it.
- @cite{haug-dalrymple-2020} consumes `**` indirectly via the bridge
  theorem `groupIdentityCond_iff_cumulative_eq` in
  `Theories/Semantics/Dynamic/PPCDRT/Cumulativity.lean`: H&D's group
  identity condition is `**` applied to *equality* on the sum-dref
  value-sets — formalising @cite{langendoen-1978}'s reciprocity-as-
  cumulativity claim within PPCDRT.
- @cite{beck-2001} §4.3 derives Weak Reciprocity from
  `**(λxλy.[R(x,y) ∧ @(x ≠ y)])(A,A)` (paper eq 120) — `**` applied
  to the verb relation strengthened by *presupposed* distinctness.
  See `Studies/Beck2001.lean`.
- @cite{sternefeld-1998} §3 derives Weak Reciprocity from
  `⟨A, A⟩ ∈ **λxy[R(x,y) ∧ x ≠ y]` (paper eq 26b) — same shape as
  Beck eq 120 but with *asserted* distinctness. In bivalent encoding
  the two predicates coincide. See
  `Studies/Sternefeld1998.lean` (which also
  defines @cite{krifka-1989}'s closure form `**` and proves the
  forward direction of its equivalence to the bidirectional-coverage
  form here).
-/

namespace Semantics.Plurality.Cumulativity

variable {A B : Type*}

/--
The cumulative operator `**` in @cite{beck-sauerland-2000}'s
bidirectional-coverage form.

Given a two-place predicate R and two pluralities x : Finset A, y : Finset B:

  **(R)(x, y) = [∀a ∈ x. ∃b ∈ y. R(a, b)] ∧ [∀b ∈ y. ∃a ∈ x. R(a, b)]

Both argument pluralities must be "covered": every atom in x is
R-related to some atom in y, and vice versa.

Heterogeneous: A and B may be different types (e.g., Elephant × Continent).
-/
def Cumulative (R : A → B → Prop) (x : Finset A) (y : Finset B) : Prop :=
  (∀ a ∈ x, ∃ b ∈ y, R a b) ∧ (∀ b ∈ y, ∃ a ∈ x, R a b)

instance Cumulative.instDecidable
    [DecidableEq A] [DecidableEq B] (R : A → B → Prop)
    [∀ a b, Decidable (R a b)] (x : Finset A) (y : Finset B) :
    Decidable (Cumulative R x y) := by
  unfold Cumulative; infer_instance

/--
Left coverage: every atom in x is R-related to some atom in y.
-/
def LeftCoverage (R : A → B → Prop) (x : Finset A) (y : Finset B) : Prop :=
  ∀ a ∈ x, ∃ b ∈ y, R a b

/--
Right coverage: every atom in y is R-related to some atom in x.
-/
def RightCoverage (R : A → B → Prop) (x : Finset A) (y : Finset B) : Prop :=
  ∀ b ∈ y, ∃ a ∈ x, R a b

/-- `**` is the conjunction of left and right coverage. -/
theorem cumulative_iff_coverages (R : A → B → Prop) (x : Finset A) (y : Finset B) :
    Cumulative R x y ↔ LeftCoverage R x y ∧ RightCoverage R x y := Iff.rfl

/-- `**` entails DIST on the left argument: if `**(R)(x, y)` then every
    atom in x is R-related to *something* in y (left universality). -/
theorem cumulative_left_universal (R : A → B → Prop) (x : Finset A) (y : Finset B)
    (h : Cumulative R x y) (a : A) (ha : a ∈ x) :
    ∃ b ∈ y, R a b :=
  h.1 a ha

/-- `**` entails DIST on the right argument: if `**(R)(x, y)` then every
    atom in y is R-related to *something* in x (right universality). -/
theorem cumulative_right_universal (R : A → B → Prop) (x : Finset A) (y : Finset B)
    (h : Cumulative R x y) (b : B) (hb : b ∈ y) :
    ∃ a ∈ x, R a b :=
  h.2 b hb

/-- Left coverage with singleton right argument reduces to universal quantification.

    When the right plurality has exactly one element y, left coverage
    becomes: ∀a ∈ x. R(a, y).

    This is one half of @cite{johnston-2023}'s "number effect": with a
    singular object DP, the cumulative reading collapses to universal
    distribution, eliminating the pairing uncertainty that motivates
    over-informative elaboration. -/
theorem singleton_right_left_coverage (R : A → B → Prop) (x : Finset A) (y : B) :
    LeftCoverage R x {y} ↔ ∀ a ∈ x, R a y := by
  unfold LeftCoverage
  constructor
  · intro h a ha
    obtain ⟨b, hb, hR⟩ := h a ha
    rw [Finset.mem_singleton.mp hb] at hR; exact hR
  · intro h a ha
    exact ⟨y, Finset.mem_singleton.mpr rfl, h a ha⟩

/-- Full `**` with singleton right argument and nonempty left argument.

    When `|Y| = 1` and `X` is nonempty, `**(R)(X, {y}) = ∀a ∈ X. R(a, y)`.
    Right coverage is trivially satisfied by any witness from X. -/
theorem singleton_right_cumulative (R : A → B → Prop) (x : Finset A) (y : B)
    (hne : x.Nonempty) :
    Cumulative R x {y} ↔ ∀ a ∈ x, R a y := by
  rw [cumulative_iff_coverages, singleton_right_left_coverage]
  refine ⟨And.left, fun h => ⟨h, ?_⟩⟩
  intro b hb
  rw [Finset.mem_singleton.mp hb]
  obtain ⟨a, ha⟩ := hne
  exact ⟨a, ha, h a ha⟩

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

def livesIn : Elephant → Continent → Prop
  | .dumbo,  .africa => True
  | .babar,  .africa => True
  | .tantor, .asia   => True
  | _,       _       => False

instance : DecidableRel livesIn := fun a b => by
  cases a <;> cases b <;> simp [livesIn] <;> infer_instance

def allElephants : Finset Elephant := Finset.univ
def africaAndAsia : Finset Continent := Finset.univ

/-- "Elephants live in Africa and Asia" is true cumulatively:
    every elephant lives in at least one continent, and each continent
    has at least one elephant. -/
example : Cumulative livesIn allElephants africaAndAsia := by decide

/-- But Tantor doesn't live in Africa — the predicate doesn't hold
    for every (elephant, continent) pair. -/
example : ¬ livesIn .tantor .africa := by decide

end ElephantExample

end Semantics.Plurality.Cumulativity
