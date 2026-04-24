import Linglib.Core.WorldTimeIndex
import Linglib.Theories.Semantics.Causation.Interpretation
import Linglib.Theories.Semantics.Causation.CCSelection

/-!
# Burning Facts: Thick and Thin Causatives
@cite{embick-2009} @cite{martin-rose-nichols-2025} @cite{rose-nichols-2021} @cite{wolff-2003}

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
| Thick → strong ASR | resultative compatibility | Causation/Studies/Semantics.Causation.ProductionDependence.lean |
| Builder `.make` | sufficiency = P-CAUSE in deterministic limit | Builder.lean |

-/

namespace Semantics.Causation.ProductionDependence

open Core (WorldTimeIndex)

open Core.Verbs (Causative)

/-! ## Causation Type

The two concepts of causation that lexical causative verbs can encode.
This is orthogonal to the `Causative` (which classifies periphrastic
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
  deriving DecidableEq, Repr

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
      *break*, *burn*, *melt*, *cut* — @cite{embick-2009} break-class.
      Compatible with strong adjectival resultatives (*burn clean*). -/
  | thickManner
  /-- Thick via state property: result state reveals production process.
      *bury* (buried → covered with earth). Not compatible with strong ASR. -/
  | thickState
  /-- Thin: result-only, no manner specification.
      *kill*, *destroy*, *damage*, *change*, *activate*. -/
  | thin
  deriving DecidableEq, Repr

/-- Is the verb thick (encodes manner of causing)? -/
def ThickThinClass.IsThick (c : ThickThinClass) : Prop :=
  c = .thickManner ∨ c = .thickState

instance : DecidablePred ThickThinClass.IsThick :=
  fun _ => inferInstanceAs (Decidable (_ ∨ _))

/-- Is the verb a causative manner verb (@cite{embick-2009} break-class)?
    These are the thick verbs whose root is an event predicate,
    compatible with strong adjectival resultatives. -/
def ThickThinClass.IsCausativeMannerVerb (c : ThickThinClass) : Prop :=
  c = .thickManner

instance : DecidablePred ThickThinClass.IsCausativeMannerVerb :=
  fun _ => inferInstanceAs (Decidable (_ = _))

/-! ## Asymmetric Entailment: P-CAUSE → D-CAUSE

In the deterministic limit, production-based causation (P-CAUSE)
entails dependence-based causation (D-CAUSE): in a single-pathway
causal model (no overdetermination), a sufficient cause is also
necessary. Under overdetermination, sufficiency and necessity come
apart — exactly when P-CAUSE and D-CAUSE diverge.

The qualitative claim is witnessed concretely via V2 `BoolSEM` models
in study files — e.g., the overdetermination case is witnessed by
`Lewis1973.Overdetermination.overdetermination_no_butfor_a` (the
chronologically-canonical owner of the symmetric-overdetermination
scenario; see also the analogous V2 sufficient-but-unnecessary
divergence in `NadathurLauer2020.Bus.cause_infelicitous_for_bus`). -/

/-! ## Production Constraint

Thick causatives preferably convey P-CAUSE (production-based causation).
This is a pragmatic constraint arising from competition between the lexical
(covert) causative and the periphrastic (overt) *cause*. -/

/-- The production constraint: thick causatives prefer production causation.

    When a thick causative is used in its physical sense, the CAUSE operator
    preferably receives a production-based interpretation. This is because
    the manner information makes P-CAUSE a salient alternative, and the
    more specific lexical form specializes in the more specific meaning. -/
def productionConstraint (cls : ThickThinClass) : CausationType :=
  if cls.IsThick then .production else .dependence

/-- Thick verbs prefer production causation. -/
theorem thick_prefers_production :
    productionConstraint .thickManner = .production ∧
    productionConstraint .thickState = .production := ⟨rfl, rfl⟩

/-- Thin verbs default to dependence causation. -/
theorem thin_defaults_dependence :
    productionConstraint .thin = .dependence := rfl

/-! ## Bridge to Causative

P-CAUSE maps to `causallySufficient` (sufficiency): production causes are sufficient.
D-CAUSE maps to `causeSem` (necessity): dependence causes are necessary.

The overt verb *cause* encodes D-CAUSE and uses `Causative.cause`.
Thick lexical causatives encode P-CAUSE and align with `Causative.make`.

Note: lexical causatives don't literally use `Causative` (which
classifies periphrastic verbs), but their internal CAUSE operator has the
same truth conditions as `causallySufficient` when P-CAUSE applies. -/

/-- Map causation type to the analogous Causative.

    This is the structural bridge: P-CAUSE's truth conditions correspond
    to sufficiency (`causallySufficient`), D-CAUSE's to necessity (`causeSem`). -/
def CausationType.analogousBuilder : CausationType → Causative
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

/-! ## Bridge to Resultatives

Thick causative manner verbs (break-class) are compatible with strong
adjectival resultatives (*break open*, *burn clean*). This connects to
the resultative infrastructure in ArgumentStructure/Studies/TheoryComparison.lean,
where the constructional CAUSE uses `Causative.make`. -/

/-- Causative manner verbs (thickManner) are compatible with strong ASR.
    This is the @cite{embick-2009} generalization formalized as a derived property.

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

/-- Production entails directness.

    When a verb encodes P-CAUSE (energy transfer), the causal relation
    is necessarily direct: for energy to transfer, there must be physical
    contact or at least no intervening causer at the same level of
    granularity. This is why the directness constraint
    holds specifically for thick causatives. -/
def productionEntailsDirectness (ct : CausationType) : Bool :=
  ct == .production

theorem production_is_direct :
    productionEntailsDirectness .production = true := rfl

theorem dependence_not_necessarily_direct :
    productionEntailsDirectness .dependence = false := rfl

/-! ## Bridge to structural queries

The structural causal model's directness and necessity directly determine
the dominant causation type. This connects model-level structural
properties to the production/dependence distinction without going through
any study-specific representation. -/

/-- Map directness/necessity to the dominant causation type.

- `direct = true` → P-CAUSE (production): a direct causal law implies
  energy/force transfer.
- `necessary = true` (without directness) → D-CAUSE (dependence):
  counterfactual dependence without direct interaction.
- Neither → no causal involvement. -/
def causationType (necessary direct : Bool) : Option CausationType :=
  if direct then some .production
  else if necessary then some .dependence
  else none

/-- Production type iff direct causal connection. -/
theorem causationType_production_iff (necessary direct : Bool) :
    causationType necessary direct = some .production ↔ direct = true := by
  simp only [causationType]
  cases direct <;> simp

/-- Dependence type iff necessary but not direct. -/
theorem causationType_dependence_iff (necessary direct : Bool) :
    causationType necessary direct = some .dependence ↔
      direct = false ∧ necessary = true := by
  simp only [causationType]
  cases direct <;> cases necessary <;> simp

/-! ## Bridge to CC-Selection

`CausationType` determines which CC-selection mode applies:
P-CAUSE (production) → completion (the cause directly completes a
sufficient set). D-CAUSE (dependence) → membership (any necessary
condition qualifies). -/

open Semantics.Causation.CCSelection

/-- Map causation type to CC-selection mode.

    - `production` → `completionOfSufficientSet`: energy-transferring
      causes complete the sufficient set directly
    - `dependence` → `memberOfSufficientSet`: counterfactual causes
      are any necessary member of a sufficient set -/
def CausationType.selectionMode : CausationType → CCSelectionMode
  | .production => .completionOfSufficientSet
  | .dependence => .memberOfSufficientSet

/-- Production uses completion selection. -/
theorem production_selects_completion :
    CausationType.production.selectionMode = .completionOfSufficientSet := rfl

/-- Dependence uses member selection. -/
theorem dependence_selects_member :
    CausationType.dependence.selectionMode = .memberOfSufficientSet := rfl

/-! `selectionMode_roundtrip` removed in Phase D-G2 — the legacy bridge
between `CCSelectionMode.toSemantics` (now deleted) and
`Causative.toSemantics` (now polymorphic V2-shaped, different signature).
The three encodings (CausationType, CCSelectionMode, Causative) remain
consistent at the enum level (`production_selects_completion` etc.); the
semantic-dispatch consistency follows from the V2 hub structure. -/

end Semantics.Causation.ProductionDependence
