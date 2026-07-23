import Linglib.Semantics.Conditionals.Counterfactual
import Linglib.Core.Logic.Trivalent.Basic
import Linglib.Core.Logic.Duality

/-!
# Quantified counterfactuals — projection-duality machinery

[ramotowska-marty-romoli-santorio-2025]

Extracted from `Semantics/Conditionals/Counterfactual.lean`
(was lines 217–492). Provides the projection-duality apparatus that
the [ramotowska-marty-romoli-santorio-2025] study file uses to
predict the strength × CF embedding pattern.

## Projection Duality: Why Strength Matters

Quantifier strength corresponds to a fundamental duality in how
semantic values project through operators:

Universal-like operators (every, no, □, ∧):
  - Conjunctive projection: need all components to succeed
  - Sensitive to negative witnesses (one failure ⇒ overall failure)
  - Fragile under heterogeneity

Existential-like operators (some, not-every, ◇, ∨):
  - Disjunctive projection: need one component to succeed
  - Sensitive to positive witnesses (one success ⇒ overall success)
  - Robust under heterogeneity

This duality manifests across natural-language semantics:

| Domain                       | Universal-like            | Existential-like          |
|------------------------------|---------------------------|---------------------------|
| Quantified counterfactuals   | Reject on mixed           | Accept on mixed           |
| Presupposition projection    | Filtering (universal)     | Existential accomm.       |
| Homogeneity                  | "The Xs P" needs all      | "Some Xs P" needs one     |
| Free Choice                  | □(A∨B) → □A∧□B            | ◇(A∨B) → ◇A∧◇B            |
| Monotonicity                 | Downward entailing        | Upward entailing          |

The selectional theory captures this because three-valued logic with
supervaluation naturally implements this projection duality.

## Quantifier Embedding

The three counterfactual theories make different predictions when
counterfactuals are embedded under quantifiers in mixed scenarios
(some individuals satisfy the consequent, others don't):

| Sentence         | Universal | Selectional | Homogeneity |
|------------------|-----------|-------------|-------------|
| Every d □→       | FALSE     | FALSE       | PRESUP FAIL |
| Some d □→        | FALSE     | TRUE        | PRESUP FAIL |
| No d □→          | TRUE      | FALSE       | PRESUP FAIL |
| Not every d □→   | TRUE      | TRUE        | PRESUP FAIL |

The universal and selectional theories agree on "every" and "not every"
but DISAGREE on "some" and "no" — the discriminating contrast tested
in [ramotowska-marty-romoli-santorio-2025].
-/

namespace Semantics.Conditionals.Counterfactual

open Trivalent (ProjectionType)

/-- Quantifier strength IS projection type. Strong quantifiers (every,
    no) use conjunctive projection; weak quantifiers (some, not-every)
    use disjunctive. -/
abbrev QStrength := ProjectionType

/-- Strong quantifiers use conjunctive projection. -/
abbrev QStrength.strong : QStrength := .conjunctive
/-- Weak quantifiers use disjunctive projection. -/
abbrev QStrength.weak : QStrength := .disjunctive
/-- Identity: projection type is already itself. -/
abbrev QStrength.toProjection (s : QStrength) : ProjectionType := s

/-- The Projection Duality Theorem.

For a list of three-valued results:
- Conjunctive projection: TRUE iff all TRUE, FALSE iff any FALSE
- Disjunctive projection: TRUE iff any TRUE, FALSE iff all FALSE

Implementation delegates to `Trivalent.aggregate`, which computes
the meet (⋀) or join (⋁) in the Trivalent lattice via foldl. -/
def projectTruthValues (proj : ProjectionType) (results : List Trivalent) : Trivalent :=
  Trivalent.aggregate proj results

/-- Conjunctive projection is fragile: one false element yields false. -/
theorem conjunctive_fragile (results : List Trivalent)
    (h : results.any (· == .false)) :
    projectTruthValues .conjunctive results ≠ .true := by
  show Trivalent.forallAll results ≠ .true
  rw [Trivalent.universal_fragile results h]; exact Trivalent.noConfusion

/-- Disjunctive projection is robust: one true element yields true. -/
theorem disjunctive_robust (results : List Trivalent)
    (h : results.any (· == .true)) :
    projectTruthValues .disjunctive results = .true :=
  Trivalent.existential_robust results h

/-- `projectTruthValues` and `aggregate` are the same operation. -/
theorem projectTruthValues_eq_aggregate (proj : ProjectionType) (l : List Trivalent) :
    projectTruthValues proj l = Trivalent.aggregate proj l := rfl

/-! ### The four embedded-quantifier operators -/

/-- Evaluate embedded counterfactual under a quantifier via projection.
    Strong quantifiers (every, no) use conjunctive projection;
    weak quantifiers (some, not every) use disjunctive projection. -/
def embeddedSelectional (s : QStrength) (results : List Trivalent) : Trivalent :=
  projectTruthValues s.toProjection results

/-- "No" quantifier: conjunctive projection over NEGATED individual
    results. "No X would V" = "Every X would NOT V". -/
def noSelectional (results : List Trivalent) : Trivalent :=
  projectTruthValues .conjunctive (results.map Trivalent.neg)

/-- "Not every" quantifier: disjunctive projection over NEGATED
    individual results. "Not every X would V" = "∃X. ¬(X would V)". -/
def notEverySelectional (results : List Trivalent) : Trivalent :=
  projectTruthValues .disjunctive (results.map Trivalent.neg)

/-! ### Selectional Theory: Embedded Determinacy

[ramotowska-marty-romoli-santorio-2025] §2.2.2: embedded
selectional counterfactuals are DETERMINATE even though unembedded
ones can be indeterminate. This is because the quantifier operates
INSIDE the scope of the selection function — within each selected
world, individual results are Bool (true/false), not Trivalent. -/

/-- **Embedded selectional determinacy**: when individual results are
    all determinate (Bool), the projected result is always determinate. -/
theorem embeddedSelectional_determinate (s : QStrength) (bs : List Bool) :
    embeddedSelectional s (bs.map Trivalent.ofBool) ≠ .indet :=
  Trivalent.aggregate_map_ofBool_ne_indet s bs

/-- **Strength determines pattern**: under selectional semantics with
    mixed Bool individual results (some true, some false):
    - Conjunctive projection (strong quantifiers) yields `.false`
    - Disjunctive projection (weak quantifiers) yields `.true` -/
theorem strength_determines_pattern (bs : List Bool)
    (h_some_true : bs.any id)
    (h_some_false : bs.any (!·)) :
    embeddedSelectional .strong (bs.map Trivalent.ofBool) = .false ∧
    embeddedSelectional .weak (bs.map Trivalent.ofBool) = .true :=
  let ⟨h_exist, h_univ⟩ := Trivalent.aggregate_map_ofBool_mixed bs h_some_true h_some_false
  ⟨h_univ, h_exist⟩

private theorem map_neg_map_ofBool (bs : List Bool) :
    (bs.map Trivalent.ofBool).map Trivalent.neg = (bs.map (!·)).map Trivalent.ofBool := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [List.map, Trivalent.neg_ofBool, ih]

private theorem any_map_not_id (bs : List Bool) :
    (bs.map (!·)).any id = bs.any (!·) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [List.map, List.any, id, ih]

private theorem any_map_not_not (bs : List Bool) :
    (bs.map (!·)).any (!·) = bs.any id := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [List.map, List.any, Bool.not_not, id, ih]

/-- **"No" in mixed scenario gives FALSE** under selectional semantics. -/
theorem no_mixed (bs : List Bool)
    (h_some_true : bs.any id) (h_some_false : bs.any (!·)) :
    noSelectional (bs.map Trivalent.ofBool) = .false := by
  unfold noSelectional
  rw [map_neg_map_ofBool]
  have h1 : (bs.map (!·)).any id := by rw [any_map_not_id]; exact h_some_false
  have h2 : (bs.map (!·)).any (!·) := by rw [any_map_not_not]; exact h_some_true
  exact (strength_determines_pattern _ h1 h2).1

/-- **"Not every" in mixed scenario gives TRUE** under selectional semantics. -/
theorem notEvery_mixed (bs : List Bool)
    (h_some_true : bs.any id) (h_some_false : bs.any (!·)) :
    notEverySelectional (bs.map Trivalent.ofBool) = .true := by
  unfold notEverySelectional
  rw [map_neg_map_ofBool]
  have h1 : (bs.map (!·)).any id := by rw [any_map_not_id]; exact h_some_false
  have h2 : (bs.map (!·)).any (!·) := by rw [any_map_not_not]; exact h_some_true
  exact (strength_determines_pattern _ h1 h2).2

/-- **All four quantifiers in mixed scenarios**: under selectional
    semantics with mixed Bool individual results, strong quantifiers
    (every, no) yield `.false` and weak quantifiers (some, not every)
    yield `.true`. -/
theorem all_four_quantifiers_mixed (bs : List Bool)
    (h_some_true : bs.any id) (h_some_false : bs.any (!·)) :
    embeddedSelectional .strong (bs.map Trivalent.ofBool) = .false ∧
    embeddedSelectional .weak (bs.map Trivalent.ofBool) = .true ∧
    noSelectional (bs.map Trivalent.ofBool) = .false ∧
    notEverySelectional (bs.map Trivalent.ofBool) = .true :=
  ⟨(strength_determines_pattern bs h_some_true h_some_false).1,
   (strength_determines_pattern bs h_some_true h_some_false).2,
   no_mixed bs h_some_true h_some_false,
   notEvery_mixed bs h_some_true h_some_false⟩

/-! ### Universal Theory: All Individual Counterfactuals False

Under the universal theory in a mixed scenario, EVERY individual
counterfactual is false. The quantifier operates over a list of
all-false values, giving DIFFERENT predictions from the selectional
theory:
- Universal: every=FALSE, some=FALSE, no=TRUE, not-every=TRUE
- Selectional: every=FALSE, some=TRUE, no=FALSE, not-every=TRUE

The theories agree on "every" and "not every" but DISAGREE on
"some" and "no" — the empirical discriminators tested in
[ramotowska-marty-romoli-santorio-2025]. -/

/-- Universal theory embedded predictions: all individual CFs false. -/
theorem universal_all_false (n : Nat) (hn : n > 0) :
    projectTruthValues .conjunctive (List.replicate n Trivalent.false) = .false ∧
    projectTruthValues .disjunctive (List.replicate n Trivalent.false) = .false := by
  refine ⟨?_, ?_⟩
  · exact Trivalent.foldl_inf_mem_false _ ⊤ (List.mem_replicate.mpr ⟨by omega, rfl⟩)
  · show (List.replicate n (⊥ : Trivalent)).foldl (· ⊔ ·) ⊥ = ⊥
    have : ∀ k, (List.replicate k (⊥ : Trivalent)).foldl (· ⊔ ·) ⊥ = ⊥ := by
      intro k; induction k with
      | zero => rfl
      | succ k ih => simp only [List.replicate_succ, List.foldl_cons, sup_idem, ih]
    exact this n

end Semantics.Conditionals.Counterfactual
