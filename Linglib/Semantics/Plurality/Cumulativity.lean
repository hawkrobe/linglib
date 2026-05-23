import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic

/-!
# Cumulative Predication
@cite{krifka-1989} @cite{sternefeld-1998} @cite{beck-sauerland-2000}

Formalises the cumulative operator `**` in the bidirectional-coverage
form. The operator originates with @cite{krifka-1989} §3 (the SUM
property `D.29` for binary relations); @cite{sternefeld-1998} §3.1
generalises to an n-ary closure operation (`***`); the
bidirectional-coverage reformulation `(∀a∈x. ∃b∈y. R(a,b)) ∧
(∀b∈y. ∃a∈x. R(a,b))` used here is from @cite{beck-sauerland-2000}.
The two formulations are equivalent on Quine-innovation domains;
`Studies/Sternefeld1998.lean::sternefeldStarStar_implies_cumulative`
proves the forward direction.

## Main declarations

* `Cumulative R x y` — bidirectional-coverage cumulative predication.
* `LeftCoverage`, `RightCoverage` — the two conjuncts; their conjunction
  IS `Cumulative` (`cumulative_iff_coverages`).
* `cumulative_left_universal`, `cumulative_right_universal` —
  per-argument distributive consequences.
* `singleton_right_cumulative` — `**` on a singleton right argument
  collapses to universal distribution.

## Implementation notes

Link's `CUM` (`Mereology.CUM`) is a *property* of denotations:
`P(x) ∧ P(y) → P(x ⊔ y)`. The `**` operator here takes a two-place
predicate and returns a new predicate with cumulative truth conditions;
the output of `**` applied to a non-cumulative predicate is itself
cumulative.

## Todo

* n-ary `***` (Sternefeld 1998 §3.1) currently lives in
  `Studies/Sternefeld1998.lean`; promote when ≥ 2 consumers.
* Schein (1993) *Plurals and Events* (bib entry pending) — the
  event-quantification alternative to the `**`-relational treatment
  of cumulativity — is not yet formalised.
-/

namespace Semantics.Plurality.Cumulativity

variable {A B : Type*}

/-! ### Bidirectional-coverage `**` -/

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
    [DecidableRel R] (x : Finset A) (y : Finset B) :
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

end Semantics.Plurality.Cumulativity
