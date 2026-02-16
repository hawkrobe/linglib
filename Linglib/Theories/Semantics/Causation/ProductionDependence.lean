import Linglib.Theories.Semantics.Causation.Builder

/-!
# Burning Facts: Thick and Thin Causatives (Martin, Rose & Nichols 2025)

Two concepts of CAUSE underlie lexical causative verb semantics:

- **P-CAUSE** (production): Energy transfer from cause to effect.
  Physical, direct, requires concrete causer. Thick causatives (*burn*,
  *break*, *melt*) preferably encode P-CAUSE.
- **D-CAUSE** (dependence): Counterfactual dependence of effect on cause.
  Abstract, allows absences/facts/degrees as causes. Thin causatives
  (*kill*, *destroy*, *damage*) are compatible with D-CAUSE.

## Key Property

P-CAUSE asymmetrically entails D-CAUSE: if x produces y (energy transfer),
then y counterfactually depends on x. But not vice versa: absences can be
d-causes without producing anything.

## Bridges to Existing Infrastructure

| Concept | Maps to | Module |
|---------|---------|--------|
| P-CAUSE (deterministic) | `causallySufficient` + directness | Sufficiency.lean |
| D-CAUSE (deterministic) | `causallyNecessary` | Necessity.lean |
| Thick → P-CAUSE preference | production constraint | (this file) |
| Thick → strong ASR | resultative compatibility | Bridge.lean |
| Builder `.make` | sufficiency = P-CAUSE in deterministic limit | Builder.lean |

## References

- Martin, F., Rose, D. & Nichols, S. (2025). Burning facts: thick and thin
  causatives. Version 1, November 23, 2025.
- Rose, D., Schaffer, J., & Nichols, S. (2021). Cause and burn.
  Cognition 215.
- Wolff, P. (2003). Direct causation in the linguistic coding and
  individuation of causal events. Cognition 88, 1-48.
- Embick, D. (2009). Roots, states, and stative passives. Abstract for
  Roots workshop, Universität Stuttgart.
-/

namespace MartinRoseNichols2025

open Core.Causation
open NadathurLauer2020.Sufficiency
open NadathurLauer2020.Necessity
open NadathurLauer2020.Builder (CausativeBuilder)

/-! ## Causation Type

The two concepts of causation that lexical causative verbs can encode.
This is orthogonal to the `CausativeBuilder` (which classifies periphrastic
causatives by force-dynamic mechanism) — it classifies how lexical
causatives encode the causal relation itself. -/

/-- Two concepts of CAUSE operating in lexical causative semantics.

    - `production`: Energy/force transfer from causer to causee (P-CAUSE).
      Requires a concrete, physical causer. Thick causatives preferably
      encode this. Entails `dependence`.
    - `dependence`: Counterfactual dependence of effect on cause (D-CAUSE).
      Compatible with abstract causes (absences, facts, degrees).
      Thin causatives and overt *cause* encode this. -/
inductive CausationType where
  /-- Production-based: energy transfer, requires concrete causer.
      *burn*, *break*, *melt* in their physical sense. -/
  | production
  /-- Dependence-based: counterfactual, allows abstract causers.
      *kill*, *destroy*, *damage*, overt *cause*. -/
  | dependence
  deriving DecidableEq, Repr, BEq

/-! ## Thick vs Thin Classification

The core empirical distinction: thick causatives encode manner of causing
(either via an event property like *break* or a state property like *bury*),
while thin causatives specify only the result state. -/

/-- Whether a lexical causative verb encodes manner of causing.

    - `thick`: Encodes manner — restricts subjects to productive causes.
      Subdivided by HOW manner is encoded (event predicate vs state property).
    - `thin`: Result-only — silent on manner, compatible with any cause type. -/
inductive ThickThinClass where
  /-- Thick via event predicate: root is a predicate of the causing event.
      *break*, *burn*, *melt*, *cut* — Embick (2009) break-class.
      Compatible with strong adjectival resultatives (*burn clean*). -/
  | thickManner
  /-- Thick via state property: result state reveals production process.
      *bury* (buried → covered with earth). Not compatible with strong ASR. -/
  | thickState
  /-- Thin: result-only, no manner specification.
      *kill*, *destroy*, *damage*, *change*, *activate*. -/
  | thin
  deriving DecidableEq, Repr, BEq

/-- Is the verb thick (encodes manner of causing)? -/
def ThickThinClass.isThick : ThickThinClass → Bool
  | .thickManner | .thickState => true
  | .thin => false

/-- Is the verb a causative manner verb (Embick 2009 break-class)?
    These are the thick verbs whose root is an event predicate,
    compatible with strong adjectival resultatives. -/
def ThickThinClass.isCausativeMannerVerb : ThickThinClass → Bool
  | .thickManner => true
  | _ => false

/-! ## Asymmetric Entailment: P-CAUSE → D-CAUSE

In the deterministic limit (our `CausalDynamics`), production-based
causation (P-CAUSE) entails dependence-based causation (D-CAUSE).

Formally: in a single-pathway causal model (no overdetermination),
if the cause is sufficient for the effect, it is also necessary.
This captures: if x produces y via direct energy transfer, removing
x would prevent y. -/

/-- In a single-pathway model (one causal law, no background alternatives),
    sufficiency implies necessity.

    This is the deterministic formalization of "P-CAUSE entails D-CAUSE":
    when there is exactly one causal pathway and no overdetermination,
    a sufficient cause is also necessary.

    Note: This fails under overdetermination (see `builders_truth_conditionally_distinct`),
    which is exactly when P-CAUSE and D-CAUSE can come apart. -/
theorem single_pathway_sufficiency_implies_necessity
    (c e : Variable) (hne : c ≠ e) :
    let dyn := CausalDynamics.mk [CausalLaw.simple c e]
    causallySufficient dyn Situation.empty c e = true →
    causallyNecessary dyn Situation.empty c e = true := by
  intro h
  simp only [causallySufficient, causallyNecessary] at *
  sorry -- TODO: Requires showing that in (Situation.empty.extend c false),
        -- the law CausalLaw.simple c e doesn't fire (c=false, law needs c=true),
        -- so normalDevelopment leaves e undetermined. Then c≠e ensures
        -- e is none (not some true) in the result. The proof requires
        -- connecting Variable's BEq to ≠ through derived DecidableEq.

/-- Concrete instance of the single-pathway entailment, fully proved.

    For specific variables a, b, the entailment P-CAUSE → D-CAUSE
    holds: sufficiency implies necessity in a single-pathway model.
    This is verified by computation. -/
theorem single_pathway_concrete :
    let a := mkVar "a"
    let b := mkVar "b"
    let dyn := CausalDynamics.mk [CausalLaw.simple a b]
    causallySufficient dyn Situation.empty a b = true ∧
    causallyNecessary dyn Situation.empty a b = true := by
  constructor <;> native_decide

/-- Under overdetermination, sufficiency does NOT imply necessity.

    This is when P-CAUSE and D-CAUSE come apart: a cause can transfer
    energy (sufficient) but the effect would have occurred anyway from
    another source (not necessary).

    Reuses the existing witness from `builders_truth_conditionally_distinct`. -/
theorem overdetermination_breaks_entailment :
    ∃ (dyn : CausalDynamics) (s : Situation) (c e : Variable),
      causallySufficient dyn s c e = true ∧
      causallyNecessary dyn s c e = false := by
  let a := mkVar "a"
  let b := mkVar "b"
  let c := mkVar "c"
  let dyn := CausalDynamics.disjunctiveCausation a b c
  let s := Situation.empty.extend b true
  use dyn, s, a, c
  constructor <;> native_decide

/-! ## Production Constraint

Thick causatives preferably convey P-CAUSE (production-based causation).
This is a pragmatic constraint arising from competition between the lexical
(covert) causative and the periphrastic (overt) *cause*. -/

/-- The production constraint: thick causatives prefer production causation.

    When a thick causative is used in its physical sense, the CAUSE operator
    preferably receives a production-based interpretation. This is because
    the manner information makes P-CAUSE a salient alternative, and the
    more specific lexical form specializes in the more specific meaning
    (Kiparsky 1982, Blutner & Solstad 2001). -/
def productionConstraint (cls : ThickThinClass) : CausationType :=
  if cls.isThick then .production else .dependence

/-- Thick verbs prefer production causation. -/
theorem thick_prefers_production :
    productionConstraint .thickManner = .production ∧
    productionConstraint .thickState = .production := ⟨rfl, rfl⟩

/-- Thin verbs default to dependence causation. -/
theorem thin_defaults_dependence :
    productionConstraint .thin = .dependence := rfl

/-! ## Bridge to CausativeBuilder

P-CAUSE maps to `makeSem` (sufficiency): production causes are sufficient.
D-CAUSE maps to `causeSem` (necessity): dependence causes are necessary.

The overt verb *cause* encodes D-CAUSE and uses `CausativeBuilder.cause`.
Thick lexical causatives encode P-CAUSE and align with `CausativeBuilder.make`.

Note: lexical causatives don't literally use `CausativeBuilder` (which
classifies periphrastic verbs), but their internal CAUSE operator has the
same truth conditions as `makeSem` when P-CAUSE applies. -/

/-- Map causation type to the analogous CausativeBuilder.

    This is the structural bridge: P-CAUSE's truth conditions correspond
    to sufficiency (`makeSem`), D-CAUSE's to necessity (`causeSem`). -/
def CausationType.analogousBuilder : CausationType → CausativeBuilder
  | .production => .make
  | .dependence => .cause

/-- Production causation is analogous to the `.make` builder. -/
theorem production_analogous_make :
    CausationType.production.analogousBuilder = .make := rfl

/-- Dependence causation is analogous to the `.cause` builder. -/
theorem dependence_analogous_cause :
    CausationType.dependence.analogousBuilder = .cause := rfl

/-- P-CAUSE's analogous builder asserts sufficiency. -/
theorem production_asserts_sufficiency :
    CausationType.production.analogousBuilder.assertsSufficiency = true := rfl

/-- D-CAUSE's analogous builder asserts necessity. -/
theorem dependence_asserts_necessity :
    CausationType.dependence.analogousBuilder.assertsNecessity = true := rfl

/-! ## Bridge to Resultatives (Embick 2009)

Thick causative manner verbs (break-class) are compatible with strong
adjectival resultatives (*break open*, *burn clean*). This connects to
the resultative infrastructure in GoldbergJackendoff2004/Bridge.lean,
where the constructional CAUSE uses `CausativeBuilder.make`. -/

/-- Causative manner verbs (thickManner) are compatible with strong ASR.
    This is the Embick (2009) generalization formalized as a derived property.

    Thin verbs and thick-state verbs (*bury*) are NOT compatible. -/
def ThickThinClass.strongASRCompatible : ThickThinClass → Bool
  | .thickManner => true
  | .thickState => false
  | .thin => false

/-- Manner verbs are ASR-compatible. -/
theorem manner_verbs_asr_compatible :
    ThickThinClass.thickManner.strongASRCompatible = true := rfl

/-- Thin verbs are NOT ASR-compatible. -/
theorem thin_verbs_not_asr :
    ThickThinClass.thin.strongASRCompatible = false := rfl

/-- Thick-state verbs (bury) are NOT ASR-compatible.
    *bury* is thick but not a causative manner verb. -/
theorem thick_state_not_asr :
    ThickThinClass.thickState.strongASRCompatible = false := rfl

/-- Production entails directness (§6).

    When a verb encodes P-CAUSE (energy transfer), the causal relation
    is necessarily direct: for energy to transfer, there must be physical
    contact or at least no intervening causer at the same level of
    granularity (Wolff 2003). This is why the directness constraint
    holds specifically for thick causatives. -/
def productionEntailsDirectness (ct : CausationType) : Bool :=
  ct == .production

theorem production_is_direct :
    productionEntailsDirectness .production = true := rfl

theorem dependence_not_necessarily_direct :
    productionEntailsDirectness .dependence = false := rfl

end MartinRoseNichols2025
