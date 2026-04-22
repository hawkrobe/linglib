/-
# Counterfactual Conditionals: Three Theories

@cite{ramotowska-marty-romoli-santorio-2025} @cite{lewis-1973}

Formalization of three competing theories of counterfactual conditionals.

## The Three Theories

1. Universal Theory (@cite{lewis-1973}/Kratzer): Universal quantification over closest A-worlds
   - ⦃A □→ B⦄_w = ∀w' ∈ closest(w, A). B(w')

2. Selectional Theory (Stalnaker): Selection function + supervaluation
   - ⦃A □→ B⦄_w = B(s(w, A)) for all legitimate selection functions s
   - Indeterminate when s₁(w,A) ∈ B but s₂(w,A) ∉ B

3. Homogeneity Theory (von Fintel, Križ): Universal + homogeneity presupposition
   - Presupposes: all closest A-worlds agree on B
   - Asserts: they all satisfy B (given the presupposition)

## Key Prediction: Quantifier Embedding

The theories diverge when counterfactuals are embedded under quantifiers
in mixed scenarios:
- Selectional: quantifier STRENGTH determines truth values (QUD-independent)
- Homogeneity: QUD × polarity interaction
- Universal: all individual CFs false → strength-independent

See `RamotowskaEtAl2025.lean` for experimental evaluation.

-/

import Mathlib.Data.Finset.Card
import Linglib.Theories.Semantics.Conditionals.Basic
import Linglib.Theories.Semantics.Conditionals.WillConditional
import Linglib.Theories.Semantics.Modality.Selectional
import Linglib.Theories.Semantics.Supervaluation.Basic
import Linglib.Core.SelectionFunction
import Linglib.Core.Causal.SEM.Counterfactual
import Linglib.Core.Logic.Truth3
import Linglib.Core.Logic.NonBivalence

namespace Semantics.Conditionals.Counterfactual

open Core (WorldTimeIndex)

open Semantics.Conditionals
open Core.Causal
open Core.Duality (Truth3 ProjectionType dist)


open Core.Order (SimilarityOrdering)


/-!
## Universal Theory
@cite{ramotowska-marty-romoli-santorio-2025}

The standard possible-worlds analysis: counterfactuals universally quantify
over the closest antecedent-worlds.

"If A were, B would" is true at w iff every closest A-world satisfies B.

This predicts:
- "Every student would pass if they studied" is FALSE if even ONE closest
  study-world for some student doesn't have them passing
-/

/--
Universal counterfactual semantics (@cite{lewis-1973}/Kratzer).

True at w iff all closest A-worlds satisfy B.
-/
def universalCounterfactual {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W) (A B : W → Prop)
    [DecidablePred A] [DecidablePred B] (w : W) : Prop :=
  ∀ w' ∈ sim.closestWorlds w (Finset.univ.filter A), B w'

instance universalCounterfactual_decidable {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W) (A B : W → Prop)
    [DecidablePred A] [DecidablePred B] (w : W) :
    Decidable (universalCounterfactual sim A B w) :=
  inferInstanceAs (Decidable (∀ _ ∈ _, _))


/-!
## Selectional Theory

Stalnaker's approach with supervaluation over ties:
1. A selection function picks THE closest antecedent-world
2. When multiple worlds are equally close (ties), supervaluate over all choices

Three-valued semantics:
- True: B holds at s(w, A) for all legitimate selection functions s
- False: B fails at s(w, A) for all legitimate selection functions s
- Indeterminate: B holds for some s but not others

This predicts:
- "Every student would pass if they studied" is INDETERMINATE when
  some students' closest study-worlds have passing, others don't
-/

-- Three-valued truth from Core.Duality.Truth3 (.gap = .indet abbreviation)

/--
Selectional counterfactual semantics (Stalnaker + supervaluation).

Returns a three-valued truth value based on agreement across selection functions.
-/
def selectionalCounterfactual {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W) (A B : W → Prop)
    [DecidablePred A] [DecidablePred B] (w : W) : Truth3 :=
  if ∀ w' ∈ sim.closestWorlds w (Finset.univ.filter A),
    B w' then .true
  else if ∀ w' ∈ sim.closestWorlds w (Finset.univ.filter A),
    ¬ B w' then .false
  else .gap

/--
Conditional Excluded Middle (CEM) holds for selectional semantics.

(A □→ B) ∨ (A □→ ¬B) is always true or gap, never false.

Proof sketch:
1. Empty closest: both vacuously true → or = true
2. All B: φ = true → or = true
3. All ¬B: ψ = true → or = true
4. Mixed: both gap → or = gap
-/
theorem cem_selectional {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W) (A B : W → Prop)
    [DecidablePred A] [DecidablePred B] (w : W) :
    let φ := selectionalCounterfactual sim A B w
    let ψ := selectionalCounterfactual sim A (¬ B ·) w
    Truth3.join φ ψ ≠ .false := by
  simp only [selectionalCounterfactual, Truth3.join]
  set cl := sim.closestWorlds w (Finset.univ.filter A)
  split_ifs <;> simp_all (config := { decide := true })


/-!
## Homogeneity Theory

Universal quantification PLUS a homogeneity presupposition:
- Presupposes: all closest A-worlds agree on B (all true or all false)
- Asserts: they all satisfy B (given the presupposition)

When the presupposition fails (mixed closest worlds), the sentence is
neither true nor false (presupposition failure).

This predicts:
- "Every student would pass if they studied" has PRESUPPOSITION FAILURE
  when students' closest study-worlds are mixed on passing
-/

/-- Presupposition status. -/
inductive PresupStatus where
  | satisfied  -- Presupposition holds
  | failed     -- Presupposition fails
  deriving Repr, DecidableEq

/-- Result of evaluating a sentence with presuppositions. -/
structure PresupResult where
  presupposition : PresupStatus
  assertion : Option Bool  -- None if presupposition fails
  deriving Repr, DecidableEq

/--
Homogeneity counterfactual semantics.

Presupposes that all closest A-worlds agree on B.
-/
def homogeneityCounterfactual {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W) (A B : W → Prop)
    [DecidablePred A] [DecidablePred B] (w : W) : PresupResult :=
  if ∀ w' ∈ sim.closestWorlds w (Finset.univ.filter A), B w' then
    { presupposition := .satisfied, assertion := some true }
  else if ∀ w' ∈ sim.closestWorlds w (Finset.univ.filter A), ¬ B w' then
    { presupposition := .satisfied, assertion := some false }
  else
    { presupposition := .failed, assertion := none }

/--
Presupposition Preservation for homogeneity semantics.

If the presupposition is satisfied for (A □→ B), it's also satisfied for (A □→ ¬B).
This is because homogeneity for B (all true or all false) implies homogeneity for ¬B.
-/
theorem presup_preserved_homogeneity {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W) (A B : W → Prop)
    [DecidablePred A] [DecidablePred B] (w : W)
    (h : (homogeneityCounterfactual sim A B w).presupposition = .satisfied) :
    (homogeneityCounterfactual sim A (¬ B ·) w).presupposition = .satisfied := by
  simp only [homogeneityCounterfactual] at *
  split_ifs at h ⊢ with h1 h2 h3 h4
  all_goals (first | rfl | simp_all)

/--
Negation Swap holds for homogeneity semantics in the non-vacuous case.

When closest worlds are non-empty and presupposition is satisfied:
  assertion(A □→ B).map (¬·) = assertion(A □→ ¬B)
-/
theorem negation_swap_homogeneity_nonvacuous {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W) (A B : W → Prop)
    [DecidablePred A] [DecidablePred B] (w : W)
    (h_presup : (homogeneityCounterfactual sim A B w).presupposition = .satisfied)
    (h_nonvac : (sim.closestWorlds w
      (Finset.univ.filter A)).Nonempty) :
    (homogeneityCounterfactual sim A B w).assertion.map (!·) =
    (homogeneityCounterfactual sim A (¬ B ·) w).assertion := by
  simp only [homogeneityCounterfactual] at *
  split_ifs at h_presup ⊢ <;> simp_all
  -- Remaining cases: h_nonvac contradicts ∀ w', w' ∉ closestWorlds
  all_goals (obtain ⟨w', hw'⟩ := h_nonvac; simp_all)


/-!
## Projection Duality: Why Strength Matters

The deeper insight behind Ramotowska et al.'s findings is that quantifier
strength corresponds to a fundamental duality in how semantic values
project through operators:

Universal-like operators (every, no, □, ∧):
  - Conjunctive projection: need all components to succeed
  - Sensitive to negative witnesses (one failure leads to overall failure)
  - Fragile under heterogeneity

Existential-like operators (some, not-every, ◇, ∨):
  - Disjunctive projection: need one component to succeed
  - Sensitive to positive witnesses (one success leads to overall success)
  - Robust under heterogeneity

This duality manifests across natural language semantics:

| Domain | Universal-like | Existential-like |
|--------|----------------|------------------|
| Quantified counterfactuals | Reject on mixed | Accept on mixed |
| Presupposition projection | Filtering (universal) | Existential accomm. |
| Homogeneity | "The Xs P" needs all | "Some Xs P" needs one |
| Free Choice | □(A∨B) → □A∧□B | ◇(A∨B) → ◇A∧◇B |
| Monotonicity | Downward entailing | Upward entailing |

The selectional theory captures this because three-valued logic with
supervaluation naturally implements this projection duality.
-/

/-- Quantifier strength IS projection type. Strong quantifiers (every, no)
    use conjunctive projection; weak quantifiers (some, not-every) use
    disjunctive. This was previously a separate `QStrength` inductive;
    now unified with `ProjectionType` from Core.Duality. -/
abbrev QStrength := ProjectionType

/-- Strong quantifiers use conjunctive projection. -/
abbrev QStrength.strong : QStrength := .conjunctive
/-- Weak quantifiers use disjunctive projection. -/
abbrev QStrength.weak : QStrength := .disjunctive
/-- Identity: projection type is already itself. -/
abbrev QStrength.toProjection (s : QStrength) : ProjectionType := s

/-- Map projection type to duality type. -/
def projToDuality : ProjectionType → Core.Duality.DualityType
  | .conjunctive => .universal
  | .disjunctive => .existential

/--
The Projection Duality Theorem.

For a list of three-valued results:
- Conjunctive projection: TRUE iff all TRUE, FALSE iff any FALSE
- Disjunctive projection: TRUE iff any TRUE, FALSE iff all FALSE

This directly explains the strength effect: conjunctive operators (strong)
are fragile under heterogeneity, disjunctive operators (weak) are robust.

Implementation delegates to `Core.Duality.aggregate`, which computes the
meet (⋀) or join (⋁) in the Truth3 lattice via foldl.
-/
def projectTruthValues (proj : ProjectionType) (results : List Truth3) : Truth3 :=
  Core.Duality.aggregate (projToDuality proj) results

/--
Conjunctive projection is fragile: one false element yields false.

When any element is false, conjunctive projection cannot return true.
-/
theorem conjunctive_fragile (results : List Truth3)
    (h : results.any (· == .false)) :
    projectTruthValues .conjunctive results ≠ .true := by
  show Core.Duality.forallAll results ≠ .true
  rw [Core.Duality.universal_fragile results h]; exact Truth3.noConfusion

/--
Disjunctive projection is robust: one true element yields true.

When any element is true, disjunctive projection returns true.
-/
theorem disjunctive_robust (results : List Truth3)
    (h : results.any (· == .true)) :
    projectTruthValues .disjunctive results = .true :=
  Core.Duality.existential_robust results h

/-- `projectTruthValues` and `aggregate` are the same operation — true
    by definition now that `projectTruthValues` delegates to `aggregate`. -/
theorem projectTruthValues_eq_aggregate (proj : ProjectionType) (l : List Truth3) :
    projectTruthValues proj l = Core.Duality.aggregate (projToDuality proj) l := rfl

/-!
## Quantifier Embedding

The three theories make different predictions when counterfactuals are
embedded under quantifiers in mixed scenarios (some individuals satisfy
the consequent, others don't).

- **Universal theory**: each individual's closest worlds include both B and ¬B
  worlds, so each individual CF is FALSE. The quantifier then
  operates over all-false values.
- **Selectional theory**: within each selected world, individual outcomes
  are Boolean (some true, some false). The quantifier evaluates within
  the world, giving determinate results. All selection functions agree.
- **Homogeneity theory**: each individual CF has presupposition failure
  (closest worlds disagree), so all quantified forms are undefined.

| Sentence         | Universal | Selectional | Homogeneity |
|------------------|-----------|-------------|-------------|
| Every d □→       | FALSE     | FALSE       | PRESUP FAIL |
| Some d □→        | FALSE     | TRUE        | PRESUP FAIL |
| No d □→          | TRUE      | FALSE       | PRESUP FAIL |
| Not every d □→   | TRUE      | TRUE        | PRESUP FAIL |

The universal and selectional theories agree on "every" and "not every"
but DISAGREE on "some" and "no".
-/

/-- Evaluate embedded counterfactual under a quantifier via projection.
    Strong quantifiers (every, no) use conjunctive projection;
    weak quantifiers (some, not every) use disjunctive projection. -/
def embeddedSelectional (s : QStrength) (results : List Truth3) : Truth3 :=
  projectTruthValues s.toProjection results

/-- "No" quantifier: conjunctive projection over NEGATED individual results.
    "No X would V" = "Every X would NOT V" = conjunctive over ¬individual. -/
def noSelectional (results : List Truth3) : Truth3 :=
  projectTruthValues .conjunctive (results.map Truth3.neg)

/-- "Not every" quantifier: disjunctive projection over NEGATED individual results.
    "Not every X would V" = "∃X. ¬(X would V)" = disjunctive over ¬individual. -/
def notEverySelectional (results : List Truth3) : Truth3 :=
  projectTruthValues .disjunctive (results.map Truth3.neg)

/-!
### Selectional Theory: Embedded Determinacy

The paper's key theoretical insight (§2.2.2): embedded
selectional counterfactuals are DETERMINATE even though unembedded
ones can be indeterminate. This is because the quantifier operates
INSIDE the scope of the selection function — within each selected world,
individual results are Bool (true/false), not Truth3.

In the win-some-lose-some lottery scenario, every candidate selection
function selects a world with mixed outcomes. The quantifier evaluates
WITHIN that world, giving a determinate result. Supervaluating over
selection functions then preserves determinacy because all give the
same quantified result.
-/

/--
**Embedded selectional determinacy**: when individual results are all
determinate (Bool), the projected result is always determinate.

This is the formal content of the paper's claim that embedded
selectional counterfactuals are determinate in mixed scenarios.

Follows directly from `global_always_determinate` in `NonBivalence.lean`:
Bool inputs → `ofBool` lattice homomorphism → no gaps. -/
theorem embeddedSelectional_determinate (s : QStrength) (bs : List Bool) :
    embeddedSelectional s (bs.map Truth3.ofBool) ≠ .gap :=
  Core.NonBivalence.global_always_determinate (projToDuality s) bs

/--
**Strength determines pattern**: under selectional semantics with mixed
Bool individual results (some true, some false):
- Conjunctive projection (strong quantifiers) yields `.false`
- Disjunctive projection (weak quantifiers) yields `.true`

Follows directly from `global_mixed_pattern` in `NonBivalence.lean`. -/
theorem strength_determines_pattern (bs : List Bool)
    (h_some_true : bs.any id)
    (h_some_false : bs.any (!·)) :
    embeddedSelectional .strong (bs.map Truth3.ofBool) = .false ∧
    embeddedSelectional .weak (bs.map Truth3.ofBool) = .true :=
  let ⟨h_exist, h_univ⟩ := Core.NonBivalence.global_mixed_pattern bs h_some_true h_some_false
  ⟨h_univ, h_exist⟩

-- Bridge: negating ofBool = ofBool of negation
private theorem map_neg_map_ofBool (bs : List Bool) :
    (bs.map Truth3.ofBool).map Truth3.neg = (bs.map (!·)).map Truth3.ofBool := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [List.map, Truth3.neg_ofBool, ih]

-- Mixed list negation preserves mixedness
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

/--
**"No" in mixed scenario gives FALSE** under selectional semantics.

"No d would B if A" = ∀d.¬CF(d). In a mixed world where some
individuals satisfy B and some don't, negating gives a mixed list
of ¬results. Conjunctive projection of a mixed list is FALSE. -/
theorem no_mixed (bs : List Bool)
    (h_some_true : bs.any id) (h_some_false : bs.any (!·)) :
    noSelectional (bs.map Truth3.ofBool) = .false := by
  unfold noSelectional
  rw [map_neg_map_ofBool]
  have h1 : (bs.map (!·)).any id := by rw [any_map_not_id]; exact h_some_false
  have h2 : (bs.map (!·)).any (!·) := by rw [any_map_not_not]; exact h_some_true
  exact (strength_determines_pattern _ h1 h2).1

/--
**"Not every" in mixed scenario gives TRUE** under selectional semantics.

"Not every d would B if A" = ∃d.¬CF(d). In a mixed world, negating
gives a mixed list. Disjunctive projection of a mixed list is TRUE. -/
theorem notEvery_mixed (bs : List Bool)
    (h_some_true : bs.any id) (h_some_false : bs.any (!·)) :
    notEverySelectional (bs.map Truth3.ofBool) = .true := by
  unfold notEverySelectional
  rw [map_neg_map_ofBool]
  have h1 : (bs.map (!·)).any id := by rw [any_map_not_id]; exact h_some_false
  have h2 : (bs.map (!·)).any (!·) := by rw [any_map_not_not]; exact h_some_true
  exact (strength_determines_pattern _ h1 h2).2

/--
**All four quantifiers in mixed scenarios**: under selectional semantics
with mixed Bool individual results, strong quantifiers (every, no) yield
`.false` and weak quantifiers (some, not every) yield `.true`. -/
theorem all_four_quantifiers_mixed (bs : List Bool)
    (h_some_true : bs.any id) (h_some_false : bs.any (!·)) :
    embeddedSelectional .strong (bs.map Truth3.ofBool) = .false ∧
    embeddedSelectional .weak (bs.map Truth3.ofBool) = .true ∧
    noSelectional (bs.map Truth3.ofBool) = .false ∧
    notEverySelectional (bs.map Truth3.ofBool) = .true :=
  ⟨(strength_determines_pattern bs h_some_true h_some_false).1,
   (strength_determines_pattern bs h_some_true h_some_false).2,
   no_mixed bs h_some_true h_some_false,
   notEvery_mixed bs h_some_true h_some_false⟩

/-!
### Universal Theory: All Individual Counterfactuals False

Under the universal theory in a mixed scenario, EVERY individual
counterfactual is false (because not all closest worlds satisfy the
consequent for any given individual). The quantifier then operates
over a list of all-false values.

This gives DIFFERENT predictions from the selectional theory:
- Universal: every=FALSE, some=FALSE, no=TRUE, not-every=TRUE
- Selectional: every=FALSE, some=TRUE, no=FALSE, not-every=TRUE

The theories agree on "every" and "not every" but DISAGREE on
"some" and "no" — the key empirical discriminators.
-/

/--
Universal theory embedded predictions: when all individual counterfactuals
are false (as the universal theory predicts in mixed scenarios),
strong quantifiers give false and weak quantifiers ALSO give false.

Contrast with the selectional theory where weak quantifiers give true. -/
theorem universal_all_false (n : Nat) (hn : n > 0) :
    projectTruthValues .conjunctive (List.replicate n Truth3.false) = .false ∧
    projectTruthValues .disjunctive (List.replicate n Truth3.false) = .false := by
  refine ⟨?_, ?_⟩
  · exact Core.Duality.foldl_inf_mem_false _ ⊤ (List.mem_replicate.mpr ⟨by omega, rfl⟩)
  · show (List.replicate n (⊥ : Truth3)).foldl (· ⊔ ·) ⊥ = ⊥
    have : ∀ k, (List.replicate k (⊥ : Truth3)).foldl (· ⊔ ·) ⊥ = ⊥ := by
      intro k; induction k with
      | zero => rfl
      | succ k ih => simp only [List.replicate_succ, List.foldl_cons, sup_idem, ih]
    exact this n


/-!
## Grounding Selection Functions in Causal Models

The selection function s(w, A) can be grounded via causal intervention:

s(w, A) = the world that results from intervening to make A true at w

This connects to @cite{nadathur-lauer-2020}:
- `normalDevelopment(s ⊕ {A = true})` gives the counterfactual A-world
- Counterfactual dependence (necessity) = selection-based conditionals

See `Theories/Semantics/Causation/` for the causal model infrastructure.
See `Phenomena/Causation/Studies/Lewis1973.lean` for the full formalization
of @cite{lewis-1973-causation}'s causal dependence, causation as transitive
closure, epiphenomena asymmetry, and bridge theorems to CC-selection.
-/

/--
Intervention-based selection: Select the world resulting from do(A).

Given a causal dynamics and situation, the selected A-world is the
result of normal development after intervening to make A true.
-/
def interventionSelection (dyn : CausalDynamics) (s : Situation)
    (antecedent : Variable) : Situation :=
  let sWithA := s.extend antecedent true
  normalDevelopment dyn sWithA

/--
Counterfactual via intervention.

"If A were true, B would be true" using causal model semantics.
-/
def causalCounterfactual (dyn : CausalDynamics) (s : Situation)
    (antecedent consequent : Variable) : Bool :=
  let counterfactualWorld := interventionSelection dyn s antecedent
  counterfactualWorld.hasValue consequent true

/--
Causal counterfactual matches necessity test for negative antecedent.

"If A were false, B would be false" = A is necessary for B.
This connects @cite{stalnaker-1968} selection to @cite{lewis-1973}/@cite{nadathur-lauer-2020} counterfactual dependence.
-/
theorem causal_counterfactual_necessity (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) :
    causalCounterfactual dyn s cause effect =
    Core.Causal.developsToTrue dyn (s.extend cause true) effect := rfl

-- ════════════════════════════════════════════════════
-- Bridge: Selectional Semantics as Supervaluation
-- ════════════════════════════════════════════════════

/-! The selectional counterfactual is literally supervaluation
    (@cite{fine-1975}) over closest worlds. Each closest world is a
    specification point — a legitimate resolution of the selection-function
    tie. When all closest worlds agree on B, the counterfactual is definite;
    when they disagree, it is indefinite.

    Now that both `selectionalCounterfactual` and `superTrue` use `Finset`,
    the connection is immediate — they are the same `∀/∃` structure over
    the same finite set. -/

open Semantics.Supervaluation (SpecSpace superTrue)

/-- **Selectional counterfactual = supervaluation over closest worlds.**
    When the closest-worlds set is non-empty, the selectional semantics
    equals `superTrue (decide ∘ B)` over the closest worlds as a
    specification space.

    This makes explicit that Stalnaker's "supervaluate over ties" IS
    Fine's supervaluation with `Spec = W` and `admissible = closest(w, A)`.
    The `decide ∘ B` reflection is needed because `superTrue` takes a
    `Bool`-valued evaluator; for any `[DecidablePred B]` this is the
    canonical Bool reflection. -/
theorem selectional_as_supervaluation {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W) (A B : W → Prop)
    [DecidablePred A] [DecidablePred B] (w : W)
    (hne : (sim.closestWorlds w
      (Finset.univ.filter A)).Nonempty) :
    selectionalCounterfactual sim A B w =
    superTrue (fun w' => decide (B w'))
      ⟨sim.closestWorlds w (Finset.univ.filter A), hne⟩ := by
  -- The two `∀` conditions on each side correspond up to `decide`.
  have h_true_iff : (∀ w' ∈ sim.closestWorlds w (Finset.univ.filter A), B w') ↔
      (∀ w' ∈ sim.closestWorlds w (Finset.univ.filter A), decide (B w') = true) := by
    constructor
    · intro h w' hw'; exact decide_eq_true (h w' hw')
    · intro h w' hw'; exact of_decide_eq_true (h w' hw')
  have h_false_iff : (∀ w' ∈ sim.closestWorlds w (Finset.univ.filter A), ¬ B w') ↔
      (∀ w' ∈ sim.closestWorlds w (Finset.univ.filter A), decide (B w') = false) := by
    constructor
    · intro h w' hw'; exact decide_eq_false (h w' hw')
    · intro h w' hw' hB
      have : decide (B w') = false := h w' hw'
      exact (of_decide_eq_false this) hB
  unfold selectionalCounterfactual superTrue
  by_cases hT : ∀ w' ∈ sim.closestWorlds w (Finset.univ.filter A), B w'
  · rw [if_pos hT, if_pos (h_true_iff.mp hT)]
  · rw [if_neg hT, if_neg (fun h => hT (h_true_iff.mpr h))]
    by_cases hF : ∀ w' ∈ sim.closestWorlds w (Finset.univ.filter A), ¬ B w'
    · rw [if_pos hF, if_pos (h_false_iff.mp hF)]
    · rw [if_neg hF, if_neg (fun h => hF (h_false_iff.mpr h))]

-- ════════════════════════════════════════════════════
-- Architectural Grounding via NonBivalence
-- ════════════════════════════════════════════════════

/-!
## Connection to NonBivalence

`projectTruthValues` now delegates directly to `Core.Duality.aggregate`,
so `embeddedSelectional_determinate` and `strength_determines_pattern` are
thin wrappers around `NonBivalence.global_always_determinate` and
`NonBivalence.global_mixed_pattern` respectively.

The `local_strength_irrelevant` theorem from `NonBivalence.lean` captures
the homogeneity theory's architecture: when all inputs are gaps, both
existential and universal aggregation return gap — strength is invisible.
-/

/-- The selectional theory's determinacy is an instance of the global
    architecture from NonBivalence: Bool inputs → determinate output. -/
theorem selectional_is_global_architecture (bs : List Bool)
    (h_some_true : bs.any id) (h_some_false : bs.any (!·)) :
    -- NonBivalence: global mixed pattern
    Core.Duality.aggregate .existential (bs.map Truth3.ofBool) = .true ∧
    Core.Duality.aggregate .universal (bs.map Truth3.ofBool) = .false :=
  Core.NonBivalence.dichotomy_global bs h_some_true h_some_false

-- ════════════════════════════════════════════════════
-- Implicature Approach (Bassi & Bar-Lev)
-- ════════════════════════════════════════════════════

/-!
## The Implicature Alternative

@cite{bassi-bar-lev-2018} propose an alternative to the selectional theory:
counterfactuals have a basic EXISTENTIAL meaning (true if some closest
A-world satisfies B), strengthened to universal by an exhaustivity
operator (EXH). In mixed scenarios, EXH strengthening fails, leaving the
basic existential meaning.

Under this approach:
- Basic meaning: ∃w ∈ closest(w,A). B(w) — EXISTENTIAL
- Strengthened: ∀w ∈ closest(w,A). B(w) — UNIVERSAL (via EXH)
- In mixed scenarios: EXH fails → basic existential → ALL quantifiers
  get existential individual results

### Wrong Prediction

The implicature theory predicts that in mixed scenarios, all quantified
counterfactuals have the SAME (existential) individual results. Since
existential is always true when B holds for some closest world:
- every(true) = true, some(true) = true, no(true) = false, not-every(true) = false

But @cite{ramotowska-marty-romoli-santorio-2025} observe:
- every = LOW (~1), some = HIGH (~97), no = LOW (~1), not-every = HIGH (~86)

The implicature theory gets "every" and "not-every" WRONG:
- Predicts: every = HIGH (∀d. true), but observed: every = LOW
- Predicts: not-every = LOW (¬∀d. true = false), but observed: not-every = HIGH
-/

/-- Under the implicature approach with all-true individual results,
    "every" is true — the OPPOSITE of the observed data (~1.5/99).
    The implicature theory predicts "every" = TRUE because individual CFs
    are all existentially true, and conjunctive projection of all-true = true.

    This contradicts @cite{ramotowska-marty-romoli-santorio-2025}: the selectional
    theory correctly predicts "every" = FALSE via conjunctive projection
    over mixed (not uniformly true) individual results. -/
theorem implicature_wrong_for_every :
    projectTruthValues .conjunctive [Truth3.true, Truth3.true] = .true := by
  decide

/-- Similarly, implicature predicts "no" = FALSE (since no(all-true) =
    ∀d.¬true = false). This agrees with the data, but for the WRONG
    REASON — the selectional theory also predicts FALSE for "no", but via
    conjunctive projection of negated mixed results, not from uniformly
    true individual CFs.

    The discriminating case is "some": implicature predicts TRUE (correct!)
    and "not-every" predicts FALSE (WRONG — observed ~86/99). -/
theorem implicature_wrong_for_notEvery :
    -- Implicature: not-every(all-true) = ∃d.¬true = FALSE (wrong!)
    -- Data: not-every ≈ 86/99 (HIGH)
    projectTruthValues .disjunctive
      ([Truth3.true, Truth3.true].map Truth3.neg) = .false := by
  decide

-- ════════════════════════════════════════════════════
-- Might Counterfactuals: Lewis vs Stalnaker
-- ════════════════════════════════════════════════════

/-!
## `Might` Counterfactuals
@cite{stalnaker-1981}

The Lewis–Stalnaker debate turns on the analysis of *might* counterfactuals.

**Lewis's definition**: "if A, might B" =_df ¬(A □→ ¬B). On this view,
`might` is an idiom — the negation of the corresponding `would not`.

**Stalnaker's objection**: Under CEM, Lewis's definition makes "if A,
might B" equivalent to "if A, would B" — collapsing the might/would
distinction. Stalnaker treats `might` as a genuine possibility operator
that takes scope *over* the conditional: ◇(A □→ B).

The three-valued selectional semantics naturally distinguishes them:
- `would`: TRUE iff all closest A-worlds satisfy B
- `might`: TRUE iff some closest A-world satisfies B (= NOT all satisfy ¬B)
-/

/-- **Lewis's `might` counterfactual**: ¬(A □→ ¬B).

Defined as the negation of the universal counterfactual with negated
consequent: "it is not the case that if A were, B would not be." -/
def lewisMight {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W) (A B : W → Prop)
    [DecidablePred A] [DecidablePred B] (w : W) : Prop :=
  ¬ universalCounterfactual sim A (¬ B ·) w

instance lewisMight_decidable {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W) (A B : W → Prop)
    [DecidablePred A] [DecidablePred B] (w : W) :
    Decidable (lewisMight sim A B w) :=
  inferInstanceAs (Decidable (¬ _))

/-- **Selectional `might` counterfactual**: true on at least one
precisification.

"If A, might B" is true iff the selectional counterfactual is not
determinately false — i.e., at least one legitimate selection function
picks a B-world. This is the existential dual of the universal `would`.

Derived from `selectionalCounterfactual` rather than inlining
`closestWorlds`, making the supervaluation connection structural. -/
def selectionalMight {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W) (A B : W → Prop)
    [DecidablePred A] [DecidablePred B] (w : W) : Prop :=
  selectionalCounterfactual sim A B w ≠ .false

instance selectionalMight_decidable {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W) (A B : W → Prop)
    [DecidablePred A] [DecidablePred B] (w : W) :
    Decidable (selectionalMight sim A B w) :=
  inferInstanceAs (Decidable (_ ≠ _))

/-- **CEM collapses Lewis's `might` into `would`.**

When the closest-worlds set is a singleton (uniqueness holds), Lewis's
`might` = ¬(all closest satisfy ¬B) = some closest satisfies B =
all closest satisfy B = `would`. The uniqueness assumption makes
¬∀¬ equivalent to ∀.

This is the problematic consequence that @cite{stalnaker-1981} argues against:
"if A, might B" should be weaker than "if A, would B", but under
uniqueness they collapse. -/
theorem lewis_might_eq_would_singleton {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W) (A B : W → Prop)
    [DecidablePred A] [DecidablePred B] (w : W)
    (h_singleton : (sim.closestWorlds w
      (Finset.univ.filter A)).card = 1) :
    lewisMight sim A B w ↔ universalCounterfactual sim A B w := by
  unfold lewisMight universalCounterfactual
  obtain ⟨w', hw'⟩ := Finset.card_eq_one.mp h_singleton
  -- ∀ in a singleton reduces to a single check
  rw [hw']
  simp only [Finset.mem_singleton, forall_eq, not_not]

/-- **CEM implies Lewis's might = would** (the general collapse).

@cite{stalnaker-1981}'s central observation: if CEM holds for the
universal theory at a world (which it does whenever closest worlds
are a singleton, but also in other cases), then Lewis's definition
of `might` as ¬(would ¬B) collapses into `would`. -/
theorem lewis_might_eq_would_cem {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W) (A B : W → Prop)
    [DecidablePred A] [DecidablePred B] (w : W)
    (h_nonempty : (sim.closestWorlds w
      (Finset.univ.filter A)).Nonempty)
    (h_cem : universalCounterfactual sim A B w ∨
             universalCounterfactual sim A (¬ B ·) w) :
    lewisMight sim A B w ↔ universalCounterfactual sim A B w := by
  unfold lewisMight universalCounterfactual at *
  rcases h_cem with h | h
  · -- all B true → ¬(all ¬B true), and we already have all B true
    refine ⟨fun _ => h, fun _ hNB => ?_⟩
    obtain ⟨w', hw'⟩ := h_nonempty
    exact (hNB w' hw') (h w' hw')
  · -- all ¬B true → both sides false (via cl nonempty)
    refine ⟨fun hMight => absurd h hMight, fun hAllB => ?_⟩
    obtain ⟨w', hw'⟩ := h_nonempty
    exact absurd (hAllB w' hw') (h w' hw')

/-- **Selectional `might` is genuinely weaker than `would`.**

There exist worlds where `might B` holds but `would B` does not:
when the closest-worlds set is mixed (some satisfy B, some don't),
the existential `might` is true but the universal `would` is indeterminate. -/
theorem selectional_might_weaker :
    ∃ (W : Type) (_ : DecidableEq W) (_ : Fintype W)
      (sim : SimilarityOrdering W)
      (A B : W → Prop) (_ : DecidablePred A) (_ : DecidablePred B) (w : W),
      selectionalMight sim A B w ∧
      selectionalCounterfactual sim A B w = .gap := by
  refine ⟨Fin 3, inferInstance, inferInstance,
    .ofBool (λ _ w₁ w₂ => w₁ == w₂) (by decide) (by decide),
    λ w => w = 1 ∨ w = 2,     -- A: both w1 and w2
    λ w => w = 1,             -- B: only w1
    inferInstance, inferInstance,
    0,                        -- actual world
    ?_, ?_⟩ <;> decide

-- ════════════════════════════════════════════════════
-- Distribution Principle
-- ════════════════════════════════════════════════════

/-!
## Distribution Principle
@cite{stalnaker-1981}

On Lewis's analysis, conditional antecedents act like necessity operators,
quantifying universally over closest A-worlds. The distribution principle

    (A □→ (B ∨ C)) ⊃ ((A □→ B) ∨ (A □→ C))

fails for universal semantics (∀ distributes over ∧ but not ∨) but holds
trivially for selectional semantics (one world, so B∨C at that world
means B or C at that world).
-/

/-- **Distribution holds for selectional semantics.**

If the selected A-world satisfies B ∨ C, then either it satisfies B
(so A □→ B) or it satisfies C (so A □→ C). -/
theorem distribution_selectional {W : Type*} [DecidableEq W] [Fintype W]
    (sim : SimilarityOrdering W) (A B C : W → Prop)
    [DecidablePred A] [DecidablePred B] [DecidablePred C] (w : W)
    (_h_unique : (sim.closestWorlds w
      (Finset.univ.filter A)).card ≤ 1)
    (h : selectionalCounterfactual sim A (λ w => B w ∨ C w) w = .true) :
    selectionalCounterfactual sim A B w = .true ∨
    selectionalCounterfactual sim A C w = .true := by
  set cl := sim.closestWorlds w _ with hcl
  unfold selectionalCounterfactual at h
  simp only [← hcl] at h
  by_cases hall : ∀ w' ∈ cl, B w' ∨ C w'
  · by_cases hempty : cl = ∅
    · -- vacuously true for both B and C
      left; unfold selectionalCounterfactual; simp [← hcl, hempty]
    · have hcard : cl.card = 1 := by
        have := Finset.card_pos.mpr (Finset.nonempty_of_ne_empty hempty)
        omega
      obtain ⟨w', hw'⟩ := Finset.card_eq_one.mp hcard
      have hbc := hall w' (by simp [hw'])
      rcases hbc with hb | hc
      · left; unfold selectionalCounterfactual
        rw [← hcl, hw']
        simp only [Finset.mem_singleton, forall_eq, hb, ite_true, if_pos]
      · right; unfold selectionalCounterfactual
        rw [← hcl, hw']
        simp only [Finset.mem_singleton, forall_eq, hc, ite_true, if_pos]
  · exfalso; simp only [if_neg hall] at h; split_ifs at h

/-- **Distribution fails for universal semantics.**

Counterexample: two closest A-worlds, one satisfying B (not C),
the other satisfying C (not B). Then A □→ (B∨C) is true (both
satisfy B∨C) but neither A □→ B nor A □→ C is true. -/
theorem distribution_fails_universal :
    ∃ (W : Type) (_ : DecidableEq W) (_ : Fintype W)
      (sim : SimilarityOrdering W)
      (A B C : W → Prop) (_ : DecidablePred A) (_ : DecidablePred B)
      (_ : DecidablePred C) (w : W),
      universalCounterfactual sim A (λ w => B w ∨ C w) w ∧
      ¬ universalCounterfactual sim A B w ∧
      ¬ universalCounterfactual sim A C w := by
  refine ⟨Fin 3, inferInstance, inferInstance,
    .ofBool (λ _ w₁ w₂ => w₁ == w₂) (by decide) (by decide),
    λ w => w = 1 ∨ w = 2,    -- A: both w1 and w2
    λ w => w = 1,            -- B: only w1
    λ w => w = 2,            -- C: only w2
    inferInstance, inferInstance, inferInstance,
    0, ?_, ?_, ?_⟩ <;> decide

-- ════════════════════════════════════════════════════
-- Single-Selection-Function Variant (Stalnaker 1968)
-- ════════════════════════════════════════════════════

/-! ## Single-Selection-Function Variant
@cite{stalnaker-1968}

Stalnaker's original counterfactual analysis used a single Stalnakerian
selection function — picking THE closest A-world — without supervaluation
over ties. This is the same `Core.SelectionFunction` infrastructure that
@cite{cariani-santorio-2018} reuse for *will* (see
`Theories/Semantics/Modality/Selectional.lean`); the mechanism is identical,
only the temporal/modal target differs.

The supervaluation variant (`selectionalCounterfactual` above) generalises
this to handle ties: each "legitimate" selection function corresponds to a
choice point, and we supervaluate over them. The bridge below shows that
when the supervaluation's closest-worlds set is the singleton chosen by a
selection function, the supervaluation analysis (`Truth3`) reduces to the
single-function analysis (`Bool`) under `Truth3.ofBool`. -/

/-- **Stalnaker's single-selection-function counterfactual** @cite{stalnaker-1968}.
    `A □→ B` is true at `w` iff `B` holds at `s(w, ‖A‖)`. This reuses the
    same `Core.SelectionFunction` infrastructure that @cite{cariani-santorio-2018}
    apply to *will* — the mechanism is identical across the two papers. -/
def stalnakerCounterfactual {W : Type*} (s : Core.SelectionFunction W)
    (A B : W → Prop) (w : W) : Prop :=
  B (s.sel w {w' | A w'})

instance stalnakerCounterfactual_decidable {W : Type*} (s : Core.SelectionFunction W)
    (A B : W → Prop) [DecidablePred B] (w : W) :
    Decidable (stalnakerCounterfactual s A B w) :=
  inferInstanceAs (Decidable (B _))

/-- **Bridge: Stalnaker = supervaluation when closest is a singleton.**

    When the supervaluation's closest-worlds set is the singleton
    `{s.sel w ‖A‖}`, the supervaluation analysis (`Truth3`) reduces
    to the single-selection-function analysis (`Bool`) under
    `Truth3.ofBool`. The supervaluation gap arises only with ties; once
    ties are resolved by the selection function, both analyses coincide. -/
theorem stalnaker_eq_selectional_singleton {W : Type*} [DecidableEq W] [Fintype W]
    (s : Core.SelectionFunction W) (sim : SimilarityOrdering W)
    (A B : W → Prop) [DecidablePred A] [DecidablePred B] (w : W)
    (h_singleton : sim.closestWorlds w (Finset.univ.filter A)
                   = {s.sel w {w' | A w'}}) :
    selectionalCounterfactual sim A B w =
    Truth3.ofBool (decide (stalnakerCounterfactual s A B w)) := by
  unfold selectionalCounterfactual stalnakerCounterfactual
  rw [h_singleton]
  by_cases hB : B (s.sel w {w' | A w'})
  · -- Both sides equal .true
    have h1 : (∀ w' ∈ ({s.sel w {w' | A w'}} : Finset W), B w') := by
      intro w' hw'; rw [Finset.mem_singleton] at hw'; rw [hw']; exact hB
    rw [if_pos h1]
    show Truth3.true = Truth3.ofBool (decide _)
    rw [decide_eq_true hB]; rfl
  · -- Both sides equal .false
    have h1 : ¬ (∀ w' ∈ ({s.sel w {w' | A w'}} : Finset W), B w') := by
      intro h; exact hB (h _ (Finset.mem_singleton.mpr rfl))
    have h2 : (∀ w' ∈ ({s.sel w {w' | A w'}} : Finset W), ¬ B w') := by
      intro w' hw'; rw [Finset.mem_singleton] at hw'; rw [hw']; exact hB
    rw [if_neg h1, if_pos h2]
    show Truth3.false = Truth3.ofBool (decide _)
    rw [decide_eq_false hB]; rfl

/-! ## Bridge: Stalnaker counterfactual = will-conditional over the universe

@cite{cariani-santorio-2018} §5.3.2 + §5.3.1 unify *will*, *would*,
will-conditionals, and Stalnaker counterfactuals under a single
`Core.SelectionFunction` substrate. Each operator differs only in its
modal parameter `f`:

- `willSem s A f w` — bare *will* with parameter `f`
- `willConditional s A B f w` — *will* with parameter `f ∩ ‖A‖`
- `stalnakerCounterfactual s A B w` — *would* with parameter `‖A‖`,
  i.e. the unrestricted parameter is the whole universe

The bridge below makes this explicit: a Stalnaker counterfactual is
exactly a will-conditional whose ambient parameter is `Set.univ`. The
*if*-clause then restricts the universe down to the antecedent's truth
set, recovering Stalnaker's `s(w, ‖A‖)`. -/

/-- **Stalnaker counterfactual = will-conditional over the universe.**

@cite{cariani-santorio-2018} §5.3.2 + §5.3.1: when the modal parameter
of the will-conditional is taken to be `Set.univ`, the Kratzer
restriction `Set.univ ∩ ‖A‖ = ‖A‖` recovers Stalnaker's selection
target. The Bool-valued `stalnakerCounterfactual` and the Prop-valued
`willConditional` thus coincide modulo the `· = true` reflection.

This is the formal payoff of the unification: bare *will* (`willSem`),
will-conditionals (`willConditional`), Stalnaker counterfactuals, and
*would*-conditionals (`wouldConditional`) all derive from one
`Core.SelectionFunction` mechanism, differing only in which modal
parameter the tense morphology supplies. -/
theorem stalnakerCounterfactual_eq_willConditional_universe
    {W : Type*} (s : Core.SelectionFunction W) (A B : W → Prop) (w : W) :
    stalnakerCounterfactual s A B w ↔
    Semantics.Conditionals.WillConditional.willConditional
      s A B Set.univ w := by
  unfold stalnakerCounterfactual
    Semantics.Conditionals.WillConditional.willConditional
    Semantics.Modality.Selectional.willSem
  rw [Set.univ_inter]

/-- **Stalnaker counterfactual = would-conditional over the universe.**

The same identity restated in *would*-conditional terms, exercising
the morphological identity `wouldConditional = willConditional`. The
counterfactual is, on the C&S analysis, a past-tense (would-) form,
so the would-conditional reading is the more natural surface gloss. -/
theorem stalnakerCounterfactual_eq_wouldConditional_universe
    {W : Type*} (s : Core.SelectionFunction W) (A B : W → Prop) (w : W) :
    stalnakerCounterfactual s A B w ↔
    Semantics.Conditionals.WillConditional.wouldConditional
      s A B Set.univ w :=
  stalnakerCounterfactual_eq_willConditional_universe s A B w

/-- **Truth3 ↔ would-conditional bridge** @cite{cariani-santorio-2018}
    §5.3.1 + §5.3.2: composing `stalnaker_eq_selectional_singleton`
    (Truth3 ↔ Bool stalnakerCounterfactual under singleton-closest) with
    `stalnakerCounterfactual_eq_wouldConditional_universe` (Bool ↔ Prop
    would-conditional under universe parameter) gives a direct bridge
    from the supervaluation-valued `selectionalCounterfactual` to the
    Prop-valued *would*-conditional of `WillConditional`.

    Under the same `h_singleton` hypothesis that resolves the Truth3
    gap (the closest-worlds set is exactly Stalnaker's selected world),
    the supervaluation analysis lands at `.true` iff the would-conditional
    holds. The two layers — Truth3 supervaluation over `Finset` and Prop
    selection-function over `Set` — collapse to the same content. -/
theorem selectional_eq_wouldConditional_singleton_universe
    {W : Type*} [DecidableEq W] [Fintype W]
    (s : Core.SelectionFunction W) (sim : SimilarityOrdering W)
    (A B : W → Prop) [DecidablePred A] [DecidablePred B] (w : W)
    (h_singleton : sim.closestWorlds w (Finset.univ.filter A)
                   = {s.sel w {w' | A w'}}) :
    selectionalCounterfactual sim A B w = .true ↔
    Semantics.Conditionals.WillConditional.wouldConditional
      s A B Set.univ w := by
  rw [stalnaker_eq_selectional_singleton s sim A B w h_singleton]
  rw [← stalnakerCounterfactual_eq_wouldConditional_universe s A B w]
  by_cases h : stalnakerCounterfactual s A B w
  · simp [decide_eq_true h, Truth3.ofBool, h]
  · simp [decide_eq_false h, Truth3.ofBool, h]

/-- A Stalnakerian selection function on `Fin 3` that prefers `1`
    whenever Centering does not force the centre. Used to witness the
    Stalnaker/Lewis would divergence below.

    `selFn w S` returns `w` if `w ∈ S` (Centering); otherwise returns
    `1` if `1 ∈ S`; otherwise picks the unique non-`w` element. -/
private noncomputable def divergeSel : Core.SelectionFunction (Fin 3) :=
  open Classical in
  { sel := fun w S => if w ∈ S then w
                      else if (1 : Fin 3) ∈ S then 1
                      else if (0 : Fin 3) ∈ S then 0
                      else 2
    inclusion := by
      intro w S hS
      by_cases hw : w ∈ S
      · simp [hw]
      · by_cases h1 : (1 : Fin 3) ∈ S
        · simp [hw, h1]
        · by_cases h0 : (0 : Fin 3) ∈ S
          · simp [hw, h1, h0]
          · simp [hw, h1, h0]
            obtain ⟨x, hx⟩ := hS
            match x, hx with
            | 0, hx => exact absurd hx h0
            | 1, hx => exact absurd hx h1
            | 2, hx => exact hx
    centering := by intro w S hw; simp [hw] }

/-- **Stalnaker–Lewis would divergence** @cite{cariani-santorio-2018}
    §5.3.2 motivation: there exist a world model, a selection function,
    a similarity ordering, an antecedent `A` and a consequent `B` such
    that the *Stalnakerian would* (single-selection-function reading)
    is `true` while the *Lewisian would* (universal over closest
    A-worlds) is `false`.

    Construction: three worlds with everyone equally close (closer ≡
    true), antecedent `A = {1, 2}`, consequent `B = {1}`. Lewis's
    closestWorlds for `A` is the whole of `A = {1, 2}`, and the
    universal `∀ w ∈ {1, 2}. B w` fails at `w = 2`. Stalnaker's
    selection (`divergeSel`) picks `1`, where `B` holds. The same
    structural source — single-valuedness of selection vs. universal
    quantification over a non-trivial closest set — drives the C&S
    *will* / `universalWill` split in
    `Semantics.Modality.Selectional`. -/
theorem stalnaker_lewis_would_diverge :
    ∃ (sim : SimilarityOrdering (Fin 3)) (A B : Fin 3 → Prop)
      (_ : DecidablePred A) (_ : DecidablePred B) (w : Fin 3),
      stalnakerCounterfactual divergeSel A B w ∧
      ¬ universalCounterfactual sim A B w := by
  classical
  refine ⟨.ofBool (fun _ _ _ => true) (by decide) (by decide),
          fun w => w = 1 ∨ w = 2,
          fun w => w = 1,
          inferInstance, inferInstance,
          0, ?_, ?_⟩
  · -- Stalnaker picks `1` from `{w | A w} = {1, 2}` (since 0 ∉ S, 1 ∈ S).
    have h0 : ¬ ((0 : Fin 3) ∈ {w : Fin 3 | w = 1 ∨ w = 2}) := by
      decide
    have h1 : (1 : Fin 3) ∈ {w : Fin 3 | w = 1 ∨ w = 2} := by
      decide
    have hsel : divergeSel.sel 0 {w : Fin 3 | w = 1 ∨ w = 2} = 1 := by
      unfold divergeSel
      simp [Core.SelectionFunction.sel, h0, h1]
    show (fun w : Fin 3 => w = 1) (divergeSel.sel 0 _)
    rw [hsel]
  · -- Universal closestWorlds = {1, 2}; the universal fails at w=2.
    decide

end Semantics.Conditionals.Counterfactual
