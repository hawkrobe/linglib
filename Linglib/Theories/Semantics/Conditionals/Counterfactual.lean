/-
# Counterfactual Conditionals: Three Theories

@cite{ramotowska-santorio-2025}

Formalization of three competing theories of counterfactual conditionals.

## The Three Theories

1. Universal Theory (Lewis/Kratzer): Universal quantification over closest A-worlds
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

import Linglib.Theories.Semantics.Conditionals.Basic
import Linglib.Theories.Semantics.Supervaluation.Basic
import Linglib.Core.StructuralEquationModel
import Linglib.Core.Logic.Truth3

namespace Semantics.Conditionals.Counterfactual

open Semantics.Conditionals
open Core.StructuralEquationModel
open Core.Duality (Truth3 ProjectionType dist)


/--
The set of closest A-worlds to w according to a similarity ordering.

In Lewis's notation: min_{≤_w}(A) = {w' ∈ A : ¬∃w'' ∈ A. w'' <_w w'}
-/
def closestWorlds {W : Type*} (sim : SimilarityOrdering W)
    (domain : Set W) (w : W) (A : Set W) : Set W :=
  let pWorlds := A ∩ domain
  { w' ∈ pWorlds | ∀ w'' ∈ pWorlds, sim.closer w w' w'' ∨ ¬sim.closer w w'' w' }

/-- Computable version for finite world spaces. -/
def closestWorldsB {W : Type*} [DecidableEq W]
    (closer : W → W → W → Bool) (domain : List W) (w : W) (A : List W) : List W :=
  let pWorlds := A.filter (domain.contains ·)
  pWorlds.filter λ w' =>
    pWorlds.all λ w'' => closer w w' w'' || !closer w w'' w'


/-!
## Universal Theory
@cite{ramotowska-santorio-2025}

The standard possible-worlds analysis: counterfactuals universally quantify
over the closest antecedent-worlds.

"If A were, B would" is true at w iff every closest A-world satisfies B.

This predicts:
- "Every student would pass if they studied" is FALSE if even ONE closest
  study-world for some student doesn't have them passing
-/

/--
Universal counterfactual semantics (Lewis/Kratzer).

True at w iff all closest A-worlds satisfy B.
-/
def universalCounterfactual {W : Type*} (sim : SimilarityOrdering W)
    (domain : Set W) (A B : W → Prop) : W → Prop :=
  λ w =>
    let closest := closestWorlds sim domain w { w' | A w' }
    closest = ∅ ∨ ∀ w' ∈ closest, B w'

/-- Decidable version. -/
def universalCounterfactualB {W : Type*} [DecidableEq W]
    (closer : W → W → W → Bool) (domain : List W) (A B : W → Bool) : W → Bool :=
  λ w =>
    let closest := closestWorldsB closer domain w (domain.filter A)
    closest.isEmpty || closest.all B


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
def selectionalCounterfactual {W : Type*} [DecidableEq W]
    (closer : W → W → W → Bool) (domain : List W) (A B : W → Bool) (w : W) : Truth3 :=
  let closest := closestWorldsB closer domain w (domain.filter A)
  match closest with
  | [] => .true  -- Vacuously true
  | _ =>
    let allTrue := closest.all B
    let allFalse := closest.all (!B ·)
    if allTrue then .true
    else if allFalse then .false
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
theorem cem_selectional {W : Type*} [DecidableEq W]
    (closer : W → W → W → Bool) (domain : List W) (A B : W → Bool) (w : W) :
    let φ := selectionalCounterfactual closer domain A B w
    let ψ := selectionalCounterfactual closer domain A (!B ·) w
    Truth3.join φ ψ ≠ .false := by
  simp only [selectionalCounterfactual]
  intro h
  -- CEM: at least one of φ, ψ is not .false
  -- The only way Truth3.join x y = .false is when x = .false and y = .false
  -- But if x = .false (for B), then all closest satisfy ¬B, so y = .true (for ¬B)
  match hc : closestWorldsB closer domain w (domain.filter A) with
  | [] => simp [hc, Truth3.join] at h
  | _::_ =>
    simp only [hc] at h
    split_ifs at h with h1 h2 h3 h4 <;> simp [Truth3.join] at h
    -- After all splits, we get contradictions from assuming both are .false
    all_goals (first | exact h | exact h.1 | exact h.2 | contradiction)


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
  deriving Repr, DecidableEq, BEq

/-- Result of evaluating a sentence with presuppositions. -/
structure PresupResult where
  presupposition : PresupStatus
  assertion : Option Bool  -- None if presupposition fails
  deriving Repr, DecidableEq

/--
Homogeneity counterfactual semantics.

Presupposes that all closest A-worlds agree on B.
-/
def homogeneityCounterfactual {W : Type*} [DecidableEq W]
    (closer : W → W → W → Bool) (domain : List W) (A B : W → Bool) (w : W) : PresupResult :=
  let closest := closestWorldsB closer domain w (domain.filter A)
  match closest with
  | [] => { presupposition := .satisfied, assertion := some true }
  | _ =>
    let allTrue := closest.all B
    let allFalse := closest.all (!B ·)
    if allTrue then
      { presupposition := .satisfied, assertion := some true }
    else if allFalse then
      { presupposition := .satisfied, assertion := some false }
    else
      -- Homogeneity failure: closest worlds don't agree
      { presupposition := .failed, assertion := none }

/--
Presupposition Preservation for homogeneity semantics.

If the presupposition is satisfied for (A □→ B), it's also satisfied for (A □→ ¬B).
This is because homogeneity for B (all true or all false) implies homogeneity for ¬B.
-/
theorem presup_preserved_homogeneity {W : Type*} [DecidableEq W]
    (closer : W → W → W → Bool) (domain : List W) (A B : W → Bool) (w : W)
    (h : (homogeneityCounterfactual closer domain A B w).presupposition = .satisfied) :
    (homogeneityCounterfactual closer domain A (!B ·) w).presupposition = .satisfied := by
  simp only [homogeneityCounterfactual] at *
  match hc : closestWorldsB closer domain w (domain.filter A) with
  | [] => simp [hc]
  | _::_ =>
    simp only [hc] at h ⊢
    split_ifs at h ⊢ with h1 h2 h3 h4
    all_goals (first | rfl | simp_all [Bool.not_not])

/--
Negation Swap holds for homogeneity semantics in the non-vacuous case.

When closest worlds are non-empty and presupposition is satisfied:
  assertion(A □→ B).map (¬·) = assertion(A □→ ¬B)
-/
theorem negation_swap_homogeneity_nonvacuous {W : Type*} [DecidableEq W]
    (closer : W → W → W → Bool) (domain : List W) (A B : W → Bool) (w : W)
    (h_presup : (homogeneityCounterfactual closer domain A B w).presupposition = .satisfied)
    (h_nonvac : (closestWorldsB closer domain w (domain.filter A)).length > 0) :
    (homogeneityCounterfactual closer domain A B w).assertion.map (!·) =
    (homogeneityCounterfactual closer domain A (!B ·) w).assertion := by
  simp only [homogeneityCounterfactual] at *
  match hc : closestWorldsB closer domain w (domain.filter A) with
  | [] => simp [hc] at h_nonvac
  | _::_ =>
    simp only [hc] at h_presup ⊢
    -- Split on the if conditions in both the original and negated formulas
    split_ifs at h_presup ⊢ <;> simp_all [Bool.not_not]


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

-- ProjectionType is now defined in Core.Duality (Core/Logic/Truth3.lean)

/-- Quantifier strength as projection type. -/
inductive QStrength where
  | strong  -- every, no: conjunctive (universal-like)
  | weak    -- some, not-every: disjunctive (existential-like)
  deriving Repr, DecidableEq, BEq

/-- Strong quantifiers use conjunctive projection; weak use disjunctive. -/
def QStrength.toProjection : QStrength → ProjectionType
  | .strong => .conjunctive
  | .weak => .disjunctive

/--
The Projection Duality Theorem.

For a list of three-valued results:
- Conjunctive projection: TRUE iff all TRUE, FALSE iff any FALSE
- Disjunctive projection: TRUE iff any TRUE, FALSE iff all FALSE

This directly explains the strength effect: conjunctive operators (strong)
are fragile under heterogeneity, disjunctive operators (weak) are robust.
-/
def projectTruthValues (proj : ProjectionType) (results : List Truth3) : Truth3 :=
  match proj with
  | .conjunctive =>
    if results.all (· == .true) then .true
    else if results.any (· == .false) then .false
    else .gap
  | .disjunctive =>
    if results.any (· == .true) then .true
    else if results.all (· == .false) then .false
    else .gap

/--
Strength effect as projection duality.

Strong quantifiers use conjunctive projection; weak use disjunctive.
-/
theorem strength_is_projection_duality (s : QStrength) (results : List Truth3) :
    projectTruthValues s.toProjection results =
    match s with
    | .strong =>
      if results.all (· == .true) then .true
      else if results.any (· == .false) then .false
      else .gap
    | .weak =>
      if results.any (· == .true) then .true
      else if results.all (· == .false) then .false
      else .gap := by
  cases s <;> simp [QStrength.toProjection, projectTruthValues]

/--
Conjunctive projection is fragile: one false element yields false.

When any element is false, conjunctive projection cannot return true.
-/
theorem conjunctive_fragile (results : List Truth3)
    (h : results.any (· == .false)) :
    projectTruthValues .conjunctive results ≠ .true := by
  unfold projectTruthValues
  simp only [ne_eq, List.any_eq_true] at h ⊢
  obtain ⟨x, hx_mem, hx_false⟩ := h
  split_ifs with h1 h2
  · -- Case: all true - but we have x with x == .false
    have hxt := List.all_eq_true.mp h1 x hx_mem
    -- hxt and hx_false contradict for any Truth3
    revert hxt hx_false
    cases x <;> decide
  · decide
  · decide

/--
Disjunctive projection is robust: one true element yields true.

When any element is true, disjunctive projection returns true.
-/
theorem disjunctive_robust (results : List Truth3)
    (h : results.any (· == .true)) :
    projectTruthValues .disjunctive results = .true := by
  unfold projectTruthValues
  simp [h]

-- PART 5b: Galois Connection (The Categorical Foundation)

/-!
## Galois Connection: Why Duality?

The projection duality is an instance of the adjoint functor relationship:

    ∃ ⊣ Δ ⊣ ∀

where Δ is the diagonal/weakening functor.

### Category-Theoretic Foundation

Given projection π: D × W → W:
- ∃_π is LEFT adjoint to pullback π*
- ∀_π is RIGHT adjoint to pullback π*

The RAPL/LAPC principle:
- Left adjoints preserve colimits (joins): ∃ is robust
- Right adjoints preserve limits (meets): ∀ is fragile

### In the Truth Value Lattice

For the three-valued lattice (false < indet < true):
- Conjunctive = infimum (⋀) = meet = limit
- Disjunctive = supremum (⋁) = join = colimit

The quantifier-projection correspondence:

| Quantifier Type | Lattice Op | Adjoint | Projection |
|-----------------|------------|---------|------------|
| every, no       | ⋀ (meet)   | RIGHT   | Fragile    |
| some, not-every | ⋁ (join)   | LEFT    | Robust     |

### Linguistic Consequence

Natural language quantifiers inherit their projection behavior from their
categorical status as adjoints. This explains cross-linguistic universals:

1. All languages have robust existentials and fragile universals
2. Polarity doesn't matter (no is strong like every) because both are ∀-like
3. Strength = adjoint type, not logical polarity

### Connection to Other Phenomena

The same adjoint duality explains:
- Presupposition projection: Universal presup (fragile) vs existential (robust)
- Free Choice: □(A∨B) → □A∧□B (right adjoint distributes over meet)
- NPI licensing: DE = right adjoint composition = license; UE = left = block
- Homogeneity: "The Xs" = hidden universal = fragile under heterogeneity

The Ramotowska et al. finding that strength determines counterfactual
judgments is thus a reflection of deep categorical structure in semantics.
-/

-- Truth3.le, .meet, .join provided by Core.Duality.Truth3

/-- Conjunctive projection computes the meet: meet(., false,.) = false -/
example : Truth3.meet .true .false = .false := rfl
example : Truth3.meet .true .gap = .gap := rfl

/-- Disjunctive projection computes the join: join(., true,.) = true -/
example : Truth3.join .false .true = .true := rfl
example : Truth3.join .false .gap = .gap := rfl

-- PART 5c: Connection to Core.Duality

/-!
## Duality Infrastructure

The projection duality used here is an instance of the general `Core.Duality`
infrastructure. See `Core/Duality.lean` for:

- `DualityType`: existential (robust) vs universal (fragile)
- `Truth3`: three-valued truth with join/meet operations
- `existential_robust`: one true → result true (left adjoint property)
- `universal_fragile`: one false → result false (right adjoint property)
- `Quantifier.duality`: classification of quantifiers by adjoint type

The counterfactual case is one instance of this
general principle, which also explains:
- Presupposition projection
- Homogeneity in plurals
- NPI licensing
- Free choice inferences
-/

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

-- Helpers: ofBool BEq reduction to Bool
private theorem ofBool_beq_true (b : Bool) : (Truth3.ofBool b == Truth3.true) = b := by
  cases b <;> rfl
private theorem ofBool_beq_false (b : Bool) : (Truth3.ofBool b == Truth3.false) = !b := by
  cases b <;> rfl

-- Bridging: List.all/any on mapped ofBool list ↔ Bool-level all/any
private theorem all_map_ofBool_beq_true (bs : List Bool) :
    (bs.map Truth3.ofBool).all (· == Truth3.true) = bs.all id := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [List.map, List.all, ofBool_beq_true, ih, id]
private theorem any_map_ofBool_beq_false (bs : List Bool) :
    (bs.map Truth3.ofBool).any (· == Truth3.false) = bs.any (!·) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [List.map, List.any, ofBool_beq_false, ih]
private theorem any_map_ofBool_beq_true (bs : List Bool) :
    (bs.map Truth3.ofBool).any (· == Truth3.true) = bs.any id := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [List.map, List.any, ofBool_beq_true, ih, id]
private theorem all_map_ofBool_beq_false (bs : List Bool) :
    (bs.map Truth3.ofBool).all (· == Truth3.false) = bs.all (!·) := by
  induction bs with
  | nil => rfl
  | cons b bs ih => simp only [List.map, List.all, ofBool_beq_false, ih]

/--
**Embedded selectional determinacy**: when individual results are all
determinate (Bool), the projected result is always determinate.

This is the formal content of the paper's claim that embedded
selectional counterfactuals are determinate in mixed scenarios. -/
theorem embeddedSelectional_determinate (s : QStrength) (bs : List Bool) :
    embeddedSelectional s (bs.map Truth3.ofBool) ≠ .gap := by
  simp only [embeddedSelectional, projectTruthValues, Truth3.gap]
  cases s <;> simp only [QStrength.toProjection]
  · -- conjunctive: gap requires ¬all_true ∧ ¬any_false — impossible for Bool
    rw [all_map_ofBool_beq_true, any_map_ofBool_beq_false]
    split_ifs with h1 h2
    · exact Truth3.noConfusion
    · exact Truth3.noConfusion
    · exfalso
      have hf : bs.all id = Bool.false := by cases bs.all id <;> simp_all
      induction bs with
      | nil => simp [List.all] at hf
      | cons b bs ih =>
        simp only [List.all, List.any, id] at hf h2 ⊢
        cases b <;> simp_all
  · -- disjunctive: gap requires ¬any_true ∧ ¬all_false — impossible for Bool
    rw [any_map_ofBool_beq_true, all_map_ofBool_beq_false]
    split_ifs with h1 h2
    · exact Truth3.noConfusion
    · exact Truth3.noConfusion
    · exfalso
      have hf : bs.any id = Bool.false := by cases bs.any id <;> simp_all
      induction bs with
      | nil => simp [List.all] at h2
      | cons b bs ih =>
        simp only [List.any, List.all, id] at hf h2 ⊢
        cases b <;> simp_all

/--
**Strength determines pattern**: under selectional semantics with mixed
Bool individual results (some true, some false):
- Conjunctive projection (strong quantifiers) yields `.false`
- Disjunctive projection (weak quantifiers) yields `.true` -/
theorem strength_determines_pattern (bs : List Bool)
    (h_some_true : bs.any id)
    (h_some_false : bs.any (!·)) :
    embeddedSelectional .strong (bs.map Truth3.ofBool) = .false ∧
    embeddedSelectional .weak (bs.map Truth3.ofBool) = .true := by
  simp only [embeddedSelectional, projectTruthValues, QStrength.toProjection]
  rw [all_map_ofBool_beq_true, any_map_ofBool_beq_false, any_map_ofBool_beq_true]
  refine ⟨?_, by simp [h_some_true]⟩
  have h_not_all : bs.all id = Bool.false := by
    by_contra h_all
    have h_all' : bs.all id = Bool.true := by cases bs.all id <;> simp_all
    induction bs with
    | nil => simp [List.any] at h_some_false
    | cons b bs ih =>
      simp only [List.all, List.any, id, Bool.and_eq_true] at h_all' h_some_false ⊢
      cases b <;> simp_all
  simp [h_not_all, h_some_false]

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
  simp only [projectTruthValues]
  constructor
  · split_ifs with h1 h2
    · exfalso; rw [List.all_eq_true] at h1
      exact absurd (h1 Truth3.false (List.mem_replicate.mpr ⟨by omega, rfl⟩)) (by decide)
    · rfl
    · exfalso; apply h2; rw [List.any_eq_true]
      exact ⟨Truth3.false, List.mem_replicate.mpr ⟨by omega, rfl⟩, by decide⟩
  · split_ifs with h1 h2
    · exfalso; rw [List.any_eq_true] at h1; obtain ⟨x, hx, hx_eq⟩ := h1
      have := (List.mem_replicate.mp hx).2; subst this; exact absurd hx_eq (by decide)
    · rfl
    · exfalso; apply h2; rw [List.all_eq_true]
      intro x hx; have := (List.mem_replicate.mp hx).2; subst this; decide


/-!
## Grounding Selection Functions in Causal Models

The selection function s(w, A) can be grounded via causal intervention:

s(w, A) = the world that results from intervening to make A true at w

This connects to @cite{nadathur-lauer-2020}:
- `normalDevelopment(s ⊕ {A = true})` gives the counterfactual A-world
- Counterfactual dependence (necessity) = selection-based conditionals

See `Theories/NadathurLauer2020/` for the causal model infrastructure.
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
This connects Stalnaker selection to Lewis/Nadathur-Lauer counterfactual dependence.
-/
theorem causal_counterfactual_necessity (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) :
    causalCounterfactual dyn s cause effect =
    Core.StructuralEquationModel.developsToTrue dyn (s.extend cause true) effect := rfl

/-- `(l.map f).all id = l.all f`: mapping then checking identity is the
    same as checking f directly. -/
private theorem all_map_id {α : Type*} (f : α → Bool) (l : List α) :
    (l.map f).all id = l.all f := by
  induction l with
  | nil => rfl
  | cons h t ih => simp [List.map_cons, List.all_cons, id, ih]

/-- `(l.map f).all (!·) = l.all (!f ·)`. -/
private theorem all_map_not {α : Type*} (f : α → Bool) (l : List α) :
    (l.map f).all (!·) = l.all (fun x => !(f x)) := by
  induction l with
  | nil => rfl
  | cons h t ih => simp [List.map_cons, List.all_cons, ih]

/-- Selectional counterfactual = `dist` applied to closest worlds mapped
    through B. The selectional theory uses the same distributivity
    operator as DIST_π (@cite{santorio-2018}). -/
theorem selectional_eq_dist {W : Type*} [DecidableEq W]
    (closer : W → W → W → Bool) (domain : List W)
    (A B : W → Bool) (w : W) :
    selectionalCounterfactual closer domain A B w =
    dist ((closestWorldsB closer domain w (domain.filter A)).map B) := by
  unfold selectionalCounterfactual dist
  simp only [all_map_id, all_map_not]
  cases closestWorldsB closer domain w (domain.filter A) with
  | nil => rfl
  | cons _ _ => rfl

-- ════════════════════════════════════════════════════
-- Bridge: Selectional Semantics as Supervaluation
-- ════════════════════════════════════════════════════

/-! The selectional counterfactual is literally supervaluation
    (@cite{fine-1975}) over closest worlds. Each closest world is a
    specification point — a legitimate resolution of the selection-function
    tie. When all closest worlds agree on B, the counterfactual is definite;
    when they disagree, it is indefinite.

    Combined with `selectional_eq_dist`, this shows three independent
    implementations are the same operator:
    - `Semantics.Supervaluation.superTrue` (Finset-based, general)
    - `Core.Duality.dist` (List-based, `Truth3.lean`)
    - `selectionalCounterfactual` (List-based, match on closest worlds) -/

open Semantics.Supervaluation (SpecSpace superTrue)

/-- Helper: `List.all` agrees with `∀ ∈ Finset` after `toFinset`. -/
private theorem list_all_iff_finset_forall {α : Type*} [DecidableEq α]
    (l : List α) (f : α → Bool) :
    l.all f = true ↔ ∀ x ∈ l.toFinset, f x = true := by
  simp [List.all_eq_true, List.mem_toFinset]

/-- **Selectional counterfactual = supervaluation over closest worlds.**
    When the closest-worlds set is non-empty, the selectional semantics
    equals `superTrue B` over the closest worlds as a specification space.

    This makes explicit that Stalnaker's "supervaluate over ties" IS
    Fine's supervaluation with `Spec = W` and `admissible = closest(w, A)`. -/
theorem selectional_as_supervaluation {W : Type*} [DecidableEq W]
    (closer : W → W → W → Bool) (domain : List W) (A B : W → Bool) (w : W)
    (hne : (closestWorldsB closer domain w (domain.filter A)).toFinset.Nonempty) :
    selectionalCounterfactual closer domain A B w =
    superTrue B ⟨(closestWorldsB closer domain w (domain.filter A)).toFinset, hne⟩ := by
  set closest := closestWorldsB closer domain w (domain.filter A) with hcl
  have hne' : closest ≠ [] := by
    intro h; simp [h] at hne
  unfold selectionalCounterfactual superTrue
  match hm : closest with
  | [] => exact absurd rfl hne'
  | _ :: _ =>
    simp only [hm]
    split_ifs <;>
      simp_all [List.all_eq_true, List.mem_toFinset, Bool.not_eq_true']

end Semantics.Conditionals.Counterfactual
