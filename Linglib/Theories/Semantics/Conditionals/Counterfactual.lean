import Mathlib.Data.Finset.Card
import Linglib.Theories.Semantics.Conditionals.Basic
import Linglib.Theories.Semantics.Conditionals.WillConditional
import Linglib.Theories.Semantics.Modality.Selectional
import Linglib.Theories.Semantics.Supervaluation.Basic
import Linglib.Theories.Semantics.Conditionals.SelectionFunction
import Linglib.Core.Logic.Truth3
import Linglib.Core.Logic.NonBivalence

/-!
# Counterfactual Conditionals: Three Theories

@cite{ramotowska-marty-romoli-santorio-2025} @cite{lewis-1973}

Formalization of three competing theories of counterfactual conditionals.

## The Three Theories

1. Universal Theory (@cite{lewis-1973}/Kratzer): Universal quantification
   over closest A-worlds.
   - ⦃A □→ B⦄_w = ∀w' ∈ closest(w, A). B(w')

2. Selectional Theory (Stalnaker): Selection function + supervaluation.
   - ⦃A □→ B⦄_w = B(s(w, A)) for all legitimate selection functions s
   - Indeterminate when s₁(w,A) ∈ B but s₂(w,A) ∉ B

3. Homogeneity Theory (von Fintel, Križ): Universal + homogeneity
   presupposition.
   - Presupposes: all closest A-worlds agree on B
   - Asserts: they all satisfy B (given the presupposition)

## Key Prediction: Quantifier Embedding

The theories diverge when counterfactuals are embedded under quantifiers
in mixed scenarios:
- Selectional: quantifier STRENGTH determines truth values (QUD-independent)
- Homogeneity: QUD × polarity interaction
- Universal: all individual CFs false → strength-independent
-/

namespace Semantics.Conditionals.Counterfactual

open Core (WorldTimeIndex)

open Semantics.Conditionals
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

-- Three-valued truth from Core.Duality.Truth3

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
  else .indet

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
## Grounding Selection Functions in Causal Models

The selection function s(w, A) can be grounded via causal intervention:

s(w, A) = the world that results from intervening to make A true at w

This connects to @cite{nadathur-lauer-2020}: `developDet M (s.extend A true)`
gives the counterfactual A-world (or, Pearl-style, `(M.intervene A true).developDet s`).
Counterfactual dependence (necessity) corresponds to selection-based conditionals.

The intervention-based counterfactual primitive lives in
`Core/Causal/V2/SEM/Counterfactual.lean` as `causallySufficient` (which
is exactly "extending with antecedent then developing produces consequent").
The full formalization of @cite{lewis-1973-causation}'s causal dependence
appears as a paper-replication study under `Phenomena/Causation/Studies/Lewis1973.lean`.
-/

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
      selectionalCounterfactual sim A B w = .indet := by
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
over ties. This is the same `Semantics.Conditionals.SelectionFunction` infrastructure that
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
    same `Semantics.Conditionals.SelectionFunction` infrastructure that @cite{cariani-santorio-2018}
    apply to *will* — the mechanism is identical across the two papers. -/
def stalnakerCounterfactual {W : Type*} (s : Semantics.Conditionals.SelectionFunction W)
    (A B : W → Prop) (w : W) : Prop :=
  B (s.sel w {w' | A w'})

instance stalnakerCounterfactual_decidable {W : Type*} (s : Semantics.Conditionals.SelectionFunction W)
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
    (s : Semantics.Conditionals.SelectionFunction W) (sim : SimilarityOrdering W)
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
`Semantics.Conditionals.SelectionFunction` substrate. Each operator differs only in its
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
`Semantics.Conditionals.SelectionFunction` mechanism, differing only in which modal
parameter the tense morphology supplies. -/
theorem stalnakerCounterfactual_eq_willConditional_universe
    {W : Type*} (s : Semantics.Conditionals.SelectionFunction W) (A B : W → Prop) (w : W) :
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
    {W : Type*} (s : Semantics.Conditionals.SelectionFunction W) (A B : W → Prop) (w : W) :
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
    (s : Semantics.Conditionals.SelectionFunction W) (sim : SimilarityOrdering W)
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
private noncomputable def divergeSel : Semantics.Conditionals.SelectionFunction (Fin 3) :=
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
      simp [Semantics.Conditionals.SelectionFunction.sel, h0, h1]
    show (fun w : Fin 3 => w = 1) (divergeSel.sel 0 _)
    rw [hsel]
  · -- Universal closestWorlds = {1, 2}; the universal fails at w=2.
    decide

end Semantics.Conditionals.Counterfactual
