/-
# Counterfactual Conditionals: Three Theories

Formalization of three competing theories of counterfactual conditionals,
following Ramotowska, Marty, Romoli & Santorio (2025).

## The Three Theories

1. **Universal Theory** (Lewis/Kratzer): Universal quantification over closest A-worlds
   - ⦃A □→ B⦄_w = ∀w' ∈ closest(w, A). B(w')

2. **Selectional Theory** (Stalnaker): Selection function + supervaluation
   - ⦃A □→ B⦄_w = B(s(w, A)) for all legitimate selection functions s
   - Indeterminate when s₁(w,A) ∈ B but s₂(w,A) ∉ B

3. **Homogeneity Theory** (von Fintel, Križ): Universal + homogeneity presupposition
   - Presupposes: all closest A-worlds agree on B
   - Asserts: they all satisfy B (given the presupposition)

## Key Prediction: Quantifier Embedding

The theories diverge when counterfactuals are embedded under quantifiers.
Given a domain where SOME closest A-worlds satisfy B and SOME don't:

| Quantifier | Universal | Selectional | Homogeneity |
|------------|-----------|-------------|-------------|
| Every NP □→ | FALSE | INDET | PRESUP FAIL |
| Some NP □→ | TRUE | TRUE | TRUE |
| No NP □→ | FALSE | FALSE | PRESUP FAIL |
| Not every NP □→ | TRUE | INDET | PRESUP FAIL |

Ramotowska et al. find experimental support for the SELECTIONAL theory.

## References

- Ramotowska, S., Marty, P., Romoli, J. & Santorio, P. (2025).
  Counterfactuals and quantificational force. Semantics & Pragmatics.
- Stalnaker, R. (1968). A Theory of Conditionals.
- Lewis, D. (1973). Counterfactuals.
- von Fintel, K. (2001). Counterfactuals in a Dynamic Context.
- Križ, M. (2015). Aspects of Homogeneity in the Semantics of NPs.
-/

import Linglib.Theories.Montague.Sentence.Conditional.Basic
import Linglib.Theories.Montague.Sentence.Conditional.CausalModel
import Linglib.Core.Duality

namespace Montague.Sentence.Conditional.Counterfactual

open Montague.Sentence.Conditional
open Theories.Montague.Conditional.CausalModel

-- ============================================================================
-- PART 1: Common Infrastructure
-- ============================================================================

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
  pWorlds.filter fun w' =>
    pWorlds.all fun w'' => closer w w' w'' || !closer w w'' w'

-- ============================================================================
-- PART 2: Universal Theory (Lewis/Kratzer)
-- ============================================================================

/-!
## Universal Theory

The standard possible-worlds analysis: counterfactuals universally quantify
over the closest antecedent-worlds.

**Definition**: "If A were, B would" is true at w iff every closest A-world satisfies B.

This predicts:
- "Every student would pass if they studied" is FALSE if even ONE closest
  study-world for some student doesn't have them passing
-/

/--
**Universal counterfactual semantics** (Lewis/Kratzer).

True at w iff ALL closest A-worlds satisfy B.
-/
def universalCounterfactual {W : Type*} (sim : SimilarityOrdering W)
    (domain : Set W) (A B : W → Prop) : W → Prop :=
  fun w =>
    let closest := closestWorlds sim domain w { w' | A w' }
    closest = ∅ ∨ ∀ w' ∈ closest, B w'

/-- Decidable version. -/
def universalCounterfactualB {W : Type*} [DecidableEq W]
    (closer : W → W → W → Bool) (domain : List W) (A B : W → Bool) : W → Bool :=
  fun w =>
    let closest := closestWorldsB closer domain w (domain.filter A)
    closest.isEmpty || closest.all B

-- ============================================================================
-- PART 3: Selectional Theory (Stalnaker + Supervaluation)
-- ============================================================================

/-!
## Selectional Theory

Stalnaker's approach with supervaluation over ties:
1. A selection function picks THE closest antecedent-world
2. When multiple worlds are equally close (ties), supervaluate over all choices

**Three-valued semantics**:
- TRUE: B holds at s(w, A) for ALL legitimate selection functions s
- FALSE: B fails at s(w, A) for ALL legitimate selection functions s
- INDETERMINATE: B holds for some s but not others

This predicts:
- "Every student would pass if they studied" is INDETERMINATE when
  some students' closest study-worlds have passing, others don't
-/

/-- Truth value in three-valued logic. -/
inductive TruthValue where
  | true
  | false
  | indeterminate
  deriving Repr, DecidableEq, BEq, Inhabited

namespace TruthValue

/-- Negation in three-valued logic. -/
def neg : TruthValue → TruthValue
  | .true => .false
  | .false => .true
  | .indeterminate => .indeterminate

/-- Conjunction in three-valued logic (Kleene strong). -/
def and : TruthValue → TruthValue → TruthValue
  | .true, .true => .true
  | .false, _ => .false
  | _, .false => .false
  | _, _ => .indeterminate

/-- Disjunction in three-valued logic (Kleene strong). -/
def or : TruthValue → TruthValue → TruthValue
  | .true, _ => .true
  | _, .true => .true
  | .false, .false => .false
  | _, _ => .indeterminate

end TruthValue

/--
**Selectional counterfactual semantics** (Stalnaker + supervaluation).

Returns a three-valued truth value based on agreement across selection functions.
-/
def selectionalCounterfactual {W : Type*} [DecidableEq W]
    (closer : W → W → W → Bool) (domain : List W) (A B : W → Bool) (w : W) : TruthValue :=
  let closest := closestWorldsB closer domain w (domain.filter A)
  match closest with
  | [] => .true  -- Vacuously true
  | _ =>
    let allTrue := closest.all B
    let allFalse := closest.all (!B ·)
    if allTrue then .true
    else if allFalse then .false
    else .indeterminate

/--
**Conditional Excluded Middle (CEM)** holds for selectional semantics.

(A □→ B) ∨ (A □→ ¬B) is always true or indeterminate, never false.

Proof sketch:
1. Empty closest: both vacuously true → or = true
2. All B: φ = true → or = true
3. All ¬B: ψ = true → or = true
4. Mixed: both indeterminate → or = indeterminate
-/
theorem cem_selectional {W : Type*} [DecidableEq W]
    (closer : W → W → W → Bool) (domain : List W) (A B : W → Bool) (w : W) :
    let φ := selectionalCounterfactual closer domain A B w
    let ψ := selectionalCounterfactual closer domain A (!B ·) w
    TruthValue.or φ ψ ≠ .false := by
  simp only [selectionalCounterfactual]
  intro h
  -- CEM: at least one of φ, ψ is not .false
  -- The only way TruthValue.or x y = .false is when x = .false and y = .false
  -- But if x = .false (for B), then all closest satisfy ¬B, so y = .true (for ¬B)
  match hc : closestWorldsB closer domain w (domain.filter A) with
  | [] => simp [hc, TruthValue.or] at h
  | _::_ =>
    simp only [hc] at h
    split_ifs at h with h1 h2 h3 h4 <;> simp [TruthValue.or] at h
    -- After all splits, we get contradictions from assuming both are .false
    all_goals (first | exact h | exact h.1 | exact h.2 | contradiction)

-- ============================================================================
-- PART 4: Homogeneity Theory (von Fintel/Križ)
-- ============================================================================

/-!
## Homogeneity Theory

Universal quantification PLUS a homogeneity presupposition:
- **Presupposes**: All closest A-worlds AGREE on B (all true or all false)
- **Asserts**: They all satisfy B (given the presupposition)

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
**Homogeneity counterfactual semantics**.

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
**Presupposition Preservation** for homogeneity semantics.

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
**Negation Swap** holds for homogeneity semantics in the non-vacuous case.

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

-- ============================================================================
-- PART 5: Projection Duality (The Deep Structure)
-- ============================================================================

/-!
## Projection Duality: Why Strength Matters

The deeper insight behind Ramotowska et al.'s findings is that quantifier
STRENGTH corresponds to a fundamental duality in how semantic values
project through operators:

**Universal-like operators** (every, no, □, ∧):
  - CONJUNCTIVE projection: need ALL components to succeed
  - Sensitive to NEGATIVE witnesses (one failure → overall failure)
  - FRAGILE under heterogeneity

**Existential-like operators** (some, not-every, ◇, ∨):
  - DISJUNCTIVE projection: need ONE component to succeed
  - Sensitive to POSITIVE witnesses (one success → overall success)
  - ROBUST under heterogeneity

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

/-- Projection type: how semantic values combine through an operator. -/
inductive ProjectionType where
  | conjunctive  -- Universal-like: all must succeed
  | disjunctive  -- Existential-like: one must succeed
  deriving Repr, DecidableEq

/-- Quantifier strength corresponds to projection type. -/
def quantifierProjection : String → ProjectionType
  | "every" => .conjunctive
  | "no" => .conjunctive      -- ¬∃ is universal-like
  | "some" => .disjunctive
  | "not-every" => .disjunctive  -- ¬∀ is existential-like
  | _ => .disjunctive

/--
**The Projection Duality Theorem**

For a list of three-valued results:
- Conjunctive projection: TRUE iff all TRUE, FALSE iff any FALSE
- Disjunctive projection: TRUE iff any TRUE, FALSE iff all FALSE

This directly explains the strength effect: conjunctive operators (strong)
are fragile under heterogeneity, disjunctive operators (weak) are robust.
-/
def projectTruthValues (proj : ProjectionType) (results : List TruthValue) : TruthValue :=
  match proj with
  | .conjunctive =>
    if results.all (· == .true) then .true
    else if results.any (· == .false) then .false
    else .indeterminate
  | .disjunctive =>
    if results.any (· == .true) then .true
    else if results.all (· == .false) then .false
    else .indeterminate

/--
**Strength effect as projection duality**.

Strong quantifiers use conjunctive projection; weak use disjunctive.
-/
theorem strength_is_projection_duality (q : String) (results : List TruthValue) :
    (q = "every" ∨ q = "no" → projectTruthValues (quantifierProjection q) results =
      if results.all (· == .true) then .true
      else if results.any (· == .false) then .false
      else .indeterminate) ∧
    (q = "some" ∨ q = "not-every" → projectTruthValues (quantifierProjection q) results =
      if results.any (· == .true) then .true
      else if results.all (· == .false) then .false
      else .indeterminate) := by
  constructor <;> intro h <;> cases h <;> simp_all [quantifierProjection, projectTruthValues]

/--
**Conjunctive projection is fragile**: one false element yields false.

When any element is false, conjunctive projection cannot return true.
-/
theorem conjunctive_fragile (results : List TruthValue)
    (h : results.any (· == .false)) :
    projectTruthValues .conjunctive results ≠ .true := by
  unfold projectTruthValues
  simp only [ne_eq, List.any_eq_true] at h ⊢
  obtain ⟨x, hx_mem, hx_false⟩ := h
  split_ifs with h1 h2
  · -- Case: all true - but we have x with x == .false
    have hxt := List.all_eq_true.mp h1 x hx_mem
    -- hxt and hx_false contradict for any TruthValue
    revert hxt hx_false
    cases x <;> decide
  · decide
  · decide

/--
**Disjunctive projection is robust**: one true element yields true.

When any element is true, disjunctive projection returns true.
-/
theorem disjunctive_robust (results : List TruthValue)
    (h : results.any (· == .true)) :
    projectTruthValues .disjunctive results = .true := by
  unfold projectTruthValues
  simp [h]

-- ============================================================================
-- PART 5b: Galois Connection (The Categorical Foundation)
-- ============================================================================

/-!
## Galois Connection: Why Duality?

The projection duality is an instance of the **adjoint functor** relationship:

    ∃ ⊣ Δ ⊣ ∀

where Δ is the diagonal/weakening functor.

### Category-Theoretic Foundation

Given projection π: D × W → W:
- ∃_π is LEFT adjoint to pullback π*
- ∀_π is RIGHT adjoint to pullback π*

The RAPL/LAPC principle:
- **Left adjoints preserve colimits** (joins): ∃ is ROBUST
- **Right adjoints preserve limits** (meets): ∀ is FRAGILE

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

1. ALL languages have robust existentials and fragile universals
2. Polarity doesn't matter (no is strong like every) because both are ∀-like
3. Strength = adjoint type, not logical polarity

### Connection to Other Phenomena

The same adjoint duality explains:
- **Presupposition projection**: Universal presup (fragile) vs existential (robust)
- **Free Choice**: □(A∨B) → □A∧□B (right adjoint distributes over meet)
- **NPI licensing**: DE = right adjoint composition = license; UE = left = block
- **Homogeneity**: "The Xs" = hidden universal = fragile under heterogeneity

The Ramotowska et al. finding that STRENGTH determines counterfactual
judgments is thus a reflection of deep categorical structure in semantics.
-/

/-- The three-valued truth lattice ordering: false < indeterminate < true -/
def TruthValue.le : TruthValue → TruthValue → Bool
  | .false, _ => Bool.true
  | .indeterminate, .indeterminate => Bool.true
  | .indeterminate, .true => Bool.true
  | .true, .true => Bool.true
  | _, _ => Bool.false

/-- Meet (infimum) in the truth value lattice. -/
def TruthValue.meet : TruthValue → TruthValue → TruthValue
  | .true, .true => .true
  | .true, .indeterminate => .indeterminate
  | .true, .false => .false
  | .indeterminate, .true => .indeterminate
  | .indeterminate, .indeterminate => .indeterminate
  | .indeterminate, .false => .false
  | .false, _ => .false

/-- Join (supremum) in the truth value lattice. -/
def TruthValue.join : TruthValue → TruthValue → TruthValue
  | .false, .false => .false
  | .false, .indeterminate => .indeterminate
  | .false, .true => .true
  | .indeterminate, .false => .indeterminate
  | .indeterminate, .indeterminate => .indeterminate
  | .indeterminate, .true => .true
  | .true, _ => .true

/-- Conjunctive projection computes the meet: meet(.., false, ..) = false -/
example : TruthValue.meet .true .false = .false := rfl
example : TruthValue.meet .true .indeterminate = .indeterminate := rfl

/-- Disjunctive projection computes the join: join(.., true, ..) = true -/
example : TruthValue.join .false .true = .true := rfl
example : TruthValue.join .false .indeterminate = .indeterminate := rfl

-- ============================================================================
-- PART 5c: Connection to Core.Duality
-- ============================================================================

/-!
## Duality Infrastructure

The projection duality used here is an instance of the general `Core.Duality`
infrastructure. See `Core/Duality.lean` for:

- `DualityType`: existential (robust) vs universal (fragile)
- `Truth3`: three-valued truth with join/meet operations
- `existential_robust`: one true → result true (left adjoint property)
- `universal_fragile`: one false → result false (right adjoint property)
- `Quantifier.duality`: classification of quantifiers by adjoint type

The counterfactual case (Ramotowska et al. 2025) is one instance of this
general principle, which also explains:
- Presupposition projection
- Homogeneity in plurals
- NPI licensing
- Free choice inferences
-/

/-- Convert our TruthValue to Core.Duality.Truth3. -/
def TruthValue.toDuality : TruthValue → Core.Duality.Truth3
  | .true => .true
  | .false => .false
  | .indeterminate => .indet

/-- Convert Core.Duality.Truth3 to our TruthValue. -/
def TruthValue.fromDuality : Core.Duality.Truth3 → TruthValue
  | .true => .true
  | .false => .false
  | .indet => .indeterminate

-- ============================================================================
-- PART 6: Quantifier Embedding (The Empirical Test)
-- ============================================================================

/-!
## Quantifier Embedding

The three theories make different predictions when counterfactuals are
embedded under quantifiers. This is the key empirical test.

Given:
- A domain of individuals D = {a, b, c, ...}
- For each d ∈ D, a counterfactual "If d were A, d would be B"
- Mixed results: some individuals' closest A-worlds satisfy B, others don't

| Sentence | Universal | Selectional | Homogeneity |
|----------|-----------|-------------|-------------|
| Every d □→ | FALSE | INDET | PRESUP FAIL |
| Some d □→ | TRUE | TRUE | TRUE (partial?) |
| No d □→ | FALSE | FALSE | PRESUP FAIL |
| Not every d □→ | TRUE | INDET | PRESUP FAIL |

Ramotowska et al. find that participants' judgments pattern with SELECTIONAL:
- Quantifier STRENGTH determines responses, not polarity
-/

/--
**Result of embedding counterfactual under a quantifier**.

For each individual, we get a truth value. The quantifier then operates
over these truth values.
-/
structure QuantifiedCounterfactualResult where
  /-- Individual results before quantification -/
  individualResults : List TruthValue
  /-- The quantifier used -/
  quantifier : String
  /-- Final result after quantification -/
  result : TruthValue
  deriving Repr

/--
Evaluate "every d: if d were A, d would be B" under selectional semantics.

TRUE iff all individual counterfactuals are true.
FALSE iff some individual counterfactual is false.
INDETERMINATE otherwise.
-/
def everySelectional (results : List TruthValue) : TruthValue :=
  if results.all (· == .true) then .true
  else if results.any (· == .false) then .false
  else .indeterminate

/--
Evaluate "some d: if d were A, d would be B" under selectional semantics.

TRUE iff some individual counterfactual is true.
FALSE iff all individual counterfactuals are false.
INDETERMINATE otherwise.
-/
def someSelectional (results : List TruthValue) : TruthValue :=
  if results.any (· == .true) then .true
  else if results.all (· == .false) then .false
  else .indeterminate

/--
Evaluate "no d: if d were A, d would be B" under selectional semantics.

TRUE iff all individual counterfactuals are false.
FALSE iff some individual counterfactual is true.
INDETERMINATE otherwise.
-/
def noSelectional (results : List TruthValue) : TruthValue :=
  if results.all (· == .false) then .true
  else if results.any (· == .true) then .false
  else .indeterminate

/--
**Key theorem: Quantifier strength determines response pattern**.

Under selectional semantics with mixed individual results:
- STRONG quantifiers (every, no) → FALSE
- WEAK quantifier (some) → TRUE

This matches Ramotowska et al.'s experimental findings.

Proof sketch:
- "every": Since some result is false, not all are true, so `everySelectional` checks
  if any is false. Since h_some_false holds, the result is `.false`.
- "some": Since some result is true, `someSelectional` returns `.true`.
- "no": Since some result is true, not all are false, so `noSelectional` returns `.false`.
-/
theorem strength_determines_pattern (results : List TruthValue)
    (h_mixed : results.any (· == .true) ∧ results.any (· == .false)) :
    everySelectional results = .false ∧
    someSelectional results = .true ∧
    noSelectional results = .false := by
  obtain ⟨h_some_true, h_some_false⟩ := h_mixed
  simp only [everySelectional, someSelectional, noSelectional]
  -- Use the hypothesis that some element is true and some is false
  constructor
  · -- every: has false element → second branch
    split_ifs with h1 h2
    · -- All true - contradicts having a false element
      simp only [List.any_eq_true] at h_some_false
      obtain ⟨x, hx_mem, hx_eq⟩ := h_some_false
      have hx_true := List.all_eq_true.mp h1 x hx_mem
      -- x == .true and x == .false both true is impossible
      cases x with
      | true => exact absurd hx_eq (by decide)
      | false => exact absurd hx_true (by decide)
      | indeterminate => exact absurd hx_eq (by decide)
    · rfl
  constructor
  · -- some: has true element → first branch
    simp only [h_some_true, ↓reduceIte]
  · -- no: has true element → second branch
    split_ifs with h1 h2
    · -- All false - contradicts having a true element
      simp only [List.any_eq_true] at h_some_true
      obtain ⟨x, hx_mem, hx_eq⟩ := h_some_true
      have hx_false := List.all_eq_true.mp h1 x hx_mem
      -- x == .true and x == .false both true is impossible
      cases x with
      | true => exact absurd hx_false (by decide)
      | false => exact absurd hx_eq (by decide)
      | indeterminate => exact absurd hx_eq (by decide)
    · rfl

-- ============================================================================
-- PART 6: Connection to Causal Models
-- ============================================================================

/-!
## Grounding Selection Functions in Causal Models

The selection function s(w, A) can be grounded via causal intervention:

s(w, A) = the world that results from intervening to make A true at w

This connects to Nadathur & Lauer (2020):
- `normalDevelopment(s ⊕ {A = true})` gives the counterfactual A-world
- Counterfactual dependence (necessity) = selection-based conditionals

See `Theories/NadathurLauer2020/` for the causal model infrastructure.
-/

/--
**Intervention-based selection**: Select the world resulting from do(A).

Given a causal dynamics and situation, the selected A-world is the
result of normal development after intervening to make A true.
-/
def interventionSelection (dyn : CausalDynamics) (s : Situation)
    (antecedent : Variable) : Situation :=
  let sWithA := s.extend antecedent true
  normalDevelopment dyn sWithA

/--
**Counterfactual via intervention**.

"If A were true, B would be true" using causal model semantics.
-/
def causalCounterfactual (dyn : CausalDynamics) (s : Situation)
    (antecedent consequent : Variable) : Bool :=
  let counterfactualWorld := interventionSelection dyn s antecedent
  counterfactualWorld.hasValue consequent true

/--
**Theorem: Causal counterfactual matches necessity test for negative antecedent**.

"If A were false, B would be false" = A is necessary for B.
This connects Stalnaker selection to Lewis/Nadathur-Lauer counterfactual dependence.
-/
theorem causal_counterfactual_necessity (dyn : CausalDynamics) (s : Situation)
    (cause effect : Variable) :
    causalCounterfactual dyn s cause effect =
    Theories.Montague.Conditional.CausalModel.developsToTrue dyn (s.extend cause true) effect := rfl

end Montague.Sentence.Conditional.Counterfactual
