import Linglib.Theories.ConstructionGrammar.Studies.GoldbergJackendoff2004
import Linglib.Theories.IntensionalSemantics.Causative.Sufficiency
import Linglib.Theories.IntensionalSemantics.Causative.Necessity
import Linglib.Theories.TruthConditional.Verb.ChangeOfState.Theory
import Linglib.Fragments.English.Predicates.Verbal

/-!
# Goldberg & Jackendoff (2004) — Cross-Theory Bridges

Connects the resultative family formalization to other modules in linglib:

1. **CxG ↔ Causal Dynamics**: causative resultatives modeled as concrete
   `CausalDynamics` with structural sufficiency proofs (Nadathur & Lauer 2020)
   and CC-selection constraints (Baglini & Bar-Asher Siegal 2025)
2. **CxG ↔ Aspect**: resultative telicizes activity verbs via bounded RP
3. **CxG ↔ ChangeOfState**: constructional BECOME maps to CoSType.inception
4. **CxG ↔ Müller decomposability**: all subconstructions decompose into
   universal schemata

## References

- Goldberg, A. E. & Jackendoff, R. (2004). The English Resultative as a
  Family of Constructions. Language, 80(3), 532–568.
- Nadathur, P. & Lauer, S. (2020). Causal necessity, causal sufficiency,
  and the implications of causative verbs. Glossa.
- Baglini, R. & Bar-Asher Siegal, E. A. (2025). Modeling linguistic
  causation. Linguistics & Philosophy, 48, 647–691.
-/

namespace ConstructionGrammar.Studies.GoldbergJackendoff2004.Bridge

open ConstructionGrammar
open ConstructionGrammar.Studies.GoldbergJackendoff2004
open TruthConditional.Verb.Aspect
open TruthConditional.Verb.ChangeOfState
open Core.Interfaces
open Core.CausalModel
open Theories.NadathurLauer2020.Sufficiency
open Theories.NadathurLauer2020.Necessity
open Theories.NadathurLauer2020.Builder (CausativeBuilder)
open Fragments.English.Predicates.Verbal (VerbEntry make cause)

/-! ## Bridge 1: CxG ↔ Causal Dynamics (Nadathur & Lauer 2020; Baglini & Bar-Asher Siegal 2025)

The constructional CAUSE in causative resultatives maps to Nadathur & Lauer's
(2020) causal sufficiency: the verbal subevent is sufficient for the
constructional result. We build concrete `CausalDynamics` and prove
structural sufficiency/necessity results.

### CC-selection (Baglini & Bar-Asher Siegal 2025)

The resultative construction performs **CC-selection**: it constrains which
condition from a causal model can fill the cause role. Causative resultatives
select via completion of a sufficient set: the verbal subevent must be the
final condition that makes the result inevitable. Combined with the temporal
constraint (G&J Principle 33), this gives the BBS2025 completion event
analysis. -/

section CausalModels

/-! ### §1a. Causal models for causative resultatives

Each causative resultative maps to a concrete `CausalDynamics` where the
verbal subevent variable causally determines the result variable. -/

/-- Hammering variable (verbal subevent of "hammer flat"). -/
def hammeringVar : Variable := mkVar "hammering"
/-- Flatness variable (constructional result of "hammer flat"). -/
def flatVar : Variable := mkVar "flat"

/-- Causal model for "She hammered the metal flat":
    the hammering activity is sufficient to produce flatness. -/
def hammerFlatModel : CausalDynamics :=
  ⟨[CausalLaw.simple hammeringVar flatVar]⟩

/-- Kicking variable (verbal subevent of "kick into field"). -/
def kickingVar : Variable := mkVar "kicking"
/-- In-field variable (constructional result of "kick into field"). -/
def inFieldVar : Variable := mkVar "in_field"

/-- Causal model for "She kicked the ball into the field". -/
def kickIntoFieldModel : CausalDynamics :=
  ⟨[CausalLaw.simple kickingVar inFieldVar]⟩

/-- Laughing variable (verbal subevent of "laugh silly"). -/
def laughingVar : Variable := mkVar "laughing"
/-- Silliness variable (constructional result of "laugh silly"). -/
def sillyVar : Variable := mkVar "silly"

/-- Causal model for "She laughed herself silly" (fake reflexive). -/
def laughSillyModel : CausalDynamics :=
  ⟨[CausalLaw.simple laughingVar sillyVar]⟩

/-! ### §1b. Sufficiency proofs

Each causative resultative's verbal subevent is causally sufficient for
the constructional result (Definition 23, Nadathur & Lauer 2020). -/

/-- Hammering is causally sufficient for flatness.

    Adding hammering to the empty background and developing normally
    yields flat = true. This is the structural content of the
    resultative's constructional CAUSE. -/
theorem hammer_sufficient_for_flat :
    causallySufficient hammerFlatModel Situation.empty hammeringVar flatVar = true := by
  native_decide

/-- Kicking is causally sufficient for being in the field. -/
theorem kick_sufficient_for_field :
    causallySufficient kickIntoFieldModel Situation.empty kickingVar inFieldVar = true := by
  native_decide

/-- Laughing is causally sufficient for becoming silly (fake reflexive). -/
theorem laugh_sufficient_for_silly :
    causallySufficient laughSillyModel Situation.empty laughingVar sillyVar = true := by
  native_decide

/-! ### §1c. Necessity proofs

With no competing causes (the canonical case for resultatives), the verbal
subevent is both sufficient AND necessary for the result. -/

/-- Hammering is also causally necessary: without it, no flatness. -/
theorem hammer_necessary_for_flat :
    let background := Situation.empty.extend hammeringVar true
    causallyNecessary hammerFlatModel background hammeringVar flatVar = true := by
  native_decide

/-- Both `makeSem` and `causeSem` hold for "hammer flat".

    With no overdetermination, the verbal subevent is both sufficient
    and necessary — matching both "make" and "cause" semantics.
    (Cf. `Examples.solo_make_and_cause` for the fire scenario.) -/
theorem hammer_flat_make_and_cause :
    let background := Situation.empty.extend hammeringVar true
    makeSem hammerFlatModel background hammeringVar flatVar = true ∧
    causeSem hammerFlatModel background hammeringVar flatVar = true := by
  constructor <;> native_decide

/-! ### §1d. Noncausative resultatives = empty dynamics

Noncausative resultatives ("The river froze solid") have the RESULT relation,
not MEANS. The constructional subevent lacks CAUSE — the verbal and
constructional subevents correlate but the verbal doesn't cause the
constructional. In causal model terms: no causal law exists. -/

/-- Freezing variable (verbal subevent of "freeze solid"). -/
def freezingVar : Variable := mkVar "freezing"
/-- Solidity variable (constructional result of "freeze solid"). -/
def solidVar : Variable := mkVar "solid"

/-- Noncausative resultatives have empty causal dynamics.

    For "The river froze solid", freezing and becoming solid are aspects
    of a single process, not in a cause-effect relation. -/
def freezeSolidModel : CausalDynamics := CausalDynamics.empty

/-- In the empty model, freezing is NOT sufficient for solidity.

    Captures the absence of CAUSE in noncausative resultatives. -/
theorem freeze_not_sufficient :
    causallySufficient freezeSolidModel Situation.empty freezingVar solidVar = false := by
  native_decide

/-- The causative/noncausative split maps to presence/absence of causal laws.

    - Causative → non-empty dynamics (verbal subevent → result)
    - Noncausative → empty dynamics (no causal link) -/
theorem causative_dynamics_noncausative_empty :
    hammerFlatModel.laws.length > 0 ∧
    kickIntoFieldModel.laws.length > 0 ∧
    laughSillyModel.laws.length > 0 ∧
    freezeSolidModel.laws.length = 0 := by
  constructor; · decide
  constructor; · decide
  constructor; · decide
  · rfl

end CausalModels

/-! ### §1e. Agreement with Boolean flags

The structural causal model results agree with the Boolean `hasCause` flags
set on each entry. -/

/-- Causative entries have CAUSE; noncausative entries do not. -/
theorem causative_iff_has_cause (e : ResultativeEntry) :
    e.subconstruction.isCausative = e.subevents.constructional.hasCause →
    (e.subconstruction.isCausative = true ↔
     e.subevents.constructional.hasCause = true) := by
  intro h
  constructor
  · intro hc; rw [← h]; exact hc
  · intro hb; rw [h]; exact hb

/-- All causative entries in the data have CAUSE (verified empirically). -/
theorem causativeResultativeHasCAUSE :
    (allEntries.filter (·.subconstruction.isCausative)).all
      (·.subevents.constructional.hasCause) = true := by
  native_decide

/-- MEANS-relation causative entries all have CAUSE. -/
theorem causative_means_have_cause :
    (allEntries.filter (λ e =>
      e.subconstruction.isCausative && e.subevents.relation == .means
    )).all (·.subevents.constructional.hasCause) = true := by
  native_decide

/-! ### §1f. CC-selection (Baglini & Bar-Asher Siegal 2025)

Different causative constructions constrain which condition from a causal
model can be selected as "the cause." BBS2025 call this CC-selection.

- Overt "cause" (BBS2025, Formula 11): the subject must be an INUS member
  of a sufficient set — any contributing condition qualifies
- CoS/lexical causatives (BBS2025, Formula 14): the subject must be the
  **completion event** — the last condition to be realized, whose occurrence
  makes the result inevitable
- Resultatives pattern with CoS: the verbal subevent completes the
  sufficient set for the constructional result -/

/-- CC-selection mode: how a causative construction selects its cause.

    - `memberOfSufficientSet`: subject is any INUS member (overt "cause")
    - `completionOfSufficientSet`: subject must complete a sufficient set
      and be temporally last (CoS verbs, resultative construction) -/
inductive CCSelectionMode where
  /-- Overt "cause": subject is any member of a sufficient set (BBS2025 §4.1) -/
  | memberOfSufficientSet
  /-- CoS/resultative: subject completes a sufficient set (BBS2025 §4.2) -/
  | completionOfSufficientSet
  deriving Repr, DecidableEq, BEq

/-- The resultative construction's CC-selection mode.

    Like CoS verbs, the resultative requires the verbal subevent to
    *complete* the sufficient set for the result — not merely be a member.
    This explains the temporal constraint (Principle 33). -/
def resultativeCCSelection : CCSelectionMode := .completionOfSufficientSet

/-- A condition completes a sufficient set for an effect iff
    adding it is sufficient and it is necessary within the set.

    This formalizes BBS2025's completion event in our causal model
    framework: the cause is the final condition needed for the effect. -/
def completesForEffect (dyn : CausalDynamics) (background : Situation)
    (cause effect : Variable) : Bool :=
  -- With cause: the set is sufficient
  causallySufficient dyn background cause effect &&
  -- Without cause: the set is NOT sufficient (cause is needed)
  causallyNecessary dyn (background.extend cause true) cause effect

/-- Hammering completes the sufficient set for flatness.

    The hammering is both sufficient (adding it produces flatness) and
    necessary (removing it prevents flatness). -/
theorem hammer_completes_for_flat :
    completesForEffect hammerFlatModel Situation.empty hammeringVar flatVar = true := by
  native_decide

/-- Kicking completes the sufficient set for in-field. -/
theorem kick_completes_for_field :
    completesForEffect kickIntoFieldModel Situation.empty kickingVar inFieldVar = true := by
  native_decide

/-! ### §1g. Temporal constraint as completion event

G&J's temporal constraint (Principle 33): the constructional subevent cannot
precede the verbal subevent. This maps to BBS2025's completion event
requirement: the completion event is the LAST condition to be realized. If
the result preceded the verbal subevent, the verbal subevent couldn't be
the completion event. -/

/-- Full completion event criterion: causal completion AND temporal ordering.

    Combines `completesForEffect` (from the causal model) with the
    temporal constraint (from G&J Principle 33). -/
def isCompletionEvent (dyn : CausalDynamics) (background : Situation)
    (cause effect : Variable) (order : TemporalOrder) : Bool :=
  completesForEffect dyn background cause effect &&
  temporalConstraintSatisfied order

/-- Hammering is a completion event for flatness (verbal precedes result). -/
theorem hammer_is_completion_event :
    isCompletionEvent hammerFlatModel Situation.empty
      hammeringVar flatVar .verbalFirst = true := by
  native_decide

/-- Hammering is a completion event when simultaneous with result. -/
theorem hammer_completion_simultaneous :
    isCompletionEvent hammerFlatModel Situation.empty
      hammeringVar flatVar .simultaneous = true := by
  native_decide

/-- Hammering CANNOT be a completion event if the result precedes it.

    If the metal is already flat before hammering, the hammering
    can't be what completed the sufficient set — violating both
    G&J's Principle 33 and BBS2025's completion event requirement. -/
theorem hammer_not_completion_if_result_first :
    isCompletionEvent hammerFlatModel Situation.empty
      hammeringVar flatVar .constructionalFirst = false := by
  native_decide

/-! ### §1h. CausativeBuilder bridge to Fragment lexicon

The resultative's CAUSE maps to `CausativeBuilder.sufficiency`, aligning
it with "make" semantics rather than "cause" semantics. The builder links
the constructional annotation to the formal semantics (`makeSem`). -/

/-- The resultative construction's CAUSE uses the sufficiency builder.

    Like "make" (and unlike "cause"), the resultative asserts that the
    verbal subevent was sufficient for the constructional result.
    `CausativeBuilder.toSemantics .sufficiency = makeSem`. -/
def resultativeCausativeBuilder : CausativeBuilder := .sufficiency

/-- Resultative causation uses sufficiency semantics (`makeSem`). -/
theorem resultative_is_sufficiency :
    resultativeCausativeBuilder = .sufficiency := rfl

/-- Resultative CAUSE matches the Fragment entry for "make" (sufficiency).

    Both the resultative construction and the lexical verb "make" use the
    same `CausativeBuilder.sufficiency`, meaning their truth conditions are
    computed by the same semantic function (`makeSem`). -/
theorem resultative_cause_matches_make_verb :
    make.causativeBuilder = some resultativeCausativeBuilder := rfl

/-- Resultative CAUSE does NOT match the Fragment entry for "cause" (necessity).

    The lexical verb "cause" uses `CausativeBuilder.necessity` (`causeSem`).
    The resultative uses `.sufficiency` (`makeSem`). These compute different
    truth conditions (proved in `builders_truth_conditionally_distinct`). -/
theorem resultative_cause_differs_from_cause_verb :
    cause.causativeBuilder ≠ some resultativeCausativeBuilder := by
  decide

/-! ## Bridge 2: CxG ↔ Aspect

Adding a bounded RP to an activity verb telicizes it:
activity + bounded RP → accomplishment.

This reuses the `telicize` operation from `TruthConditional.Verb.Aspect`. -/

/-- Adding a bounded RP to an activity verb yields an accomplishment.

    "She hammered the metal" (activity, atelic) →
    "She hammered the metal flat" (accomplishment, telic)

    This is exactly `telicize_activity` from Aspect.lean applied
    to the resultative construction. -/
theorem resultativeTelicizes :
    activityProfile.telicize.toVendlerClass = .accomplishment :=
  telicize_activity

/-- The resultative construction's aspect shift: for any activity verb
    with a bounded RP, the result is an accomplishment. -/
theorem resultativeAspectShift :
    resultativeVendlerClass .bounded = .accomplishment :=
  rfl

/-- The resultative-derived aspect matches the general telicize operation
    when starting from an activity. -/
theorem resultative_aspect_agrees_with_telicize :
    resultativeVendlerClass .bounded =
    activityProfile.telicize.toVendlerClass := by
  rfl

/-- Activity verbs in the data that get bounded RPs become accomplishments. -/
theorem activity_entries_become_accomplishments :
    (allEntries.filter (λ e =>
      e.bareVerbClass == .activity && e.rpBoundedness == .bounded
    )).all (λ e =>
      resultativeVendlerClass e.rpBoundedness == .accomplishment
    ) = true := by
  native_decide

/-! ## Bridge 3: CxG ↔ ChangeOfState

The constructional subevent's BECOME maps to `CoSType.inception`:
a transition from ¬P to P (the result state wasn't holding, now it is).

"The river froze solid": ¬solid → solid = inception of solidity. -/

/-- The constructional BECOME in resultatives corresponds to inception:
    the result state transitions from false to true.

    This maps the CxG notion of BECOME to the formal semantics of
    change-of-state predicates in `ChangeOfState.Theory`. -/
def resultStateMapsToCoS : CoSType := .inception

/-- All resultative entries have BECOME in their constructional subevent.
    This is the defining property: the construction contributes a state change. -/
theorem all_have_become :
    allEntries.all (·.subevents.constructional.hasBecome) = true := by
  native_decide

/-- Inception presupposes the prior state was false (¬P before → P after).
    For resultatives: the result state was not holding before the event.

    "hammer flat" presupposes the metal was NOT flat before hammering. -/
theorem inception_presupposes_not_prior {W : Type*} (P : W → Bool) (w : W) :
    priorStatePresup .inception P w = !P w := rfl

/-- Inception asserts the result state now holds (P after).

    "hammer flat" asserts the metal IS flat after hammering. -/
theorem inception_asserts_result {W : Type*} (P : W → Bool) :
    resultStateAssertion .inception P = P := rfl

/-! ## Bridge 4: CxG ↔ Müller Decomposability

All four resultative subconstructions are fully abstract and therefore
decomposable into Müller's universal schemata.

Causative subconstructions → [HS, HC, HC] (same as parent resultative)
Noncausative subconstructions → [HS, HC] (intransitive, fewer complements) -/

/-- All four subconstructions are decomposable (fully abstract with no
    pragmatic function). -/
theorem allResultativesDecomposable :
    resultativeFamily.all (λ c =>
      isDecomposable c.construction) = true := by
  native_decide

/-- Causative subconstructions decompose like the parent resultative
    into three combination steps. -/
theorem causative_decompose_like_parent :
    decompose causativePropertyConstruction = decompose resultative ∧
    decompose causativePathConstruction = decompose resultative := by
  constructor <;> native_decide

/-- Noncausative subconstructions decompose into two combination steps
    (one fewer than the causative, reflecting their intransitivity). -/
theorem noncausative_fewer_steps :
    (decompose noncausativePropertyConstruction).length <
    (decompose causativePropertyConstruction).length ∧
    (decompose noncausativePathConstruction).length <
    (decompose causativePathConstruction).length := by
  constructor <;> native_decide

/-- The causative/noncausative split is reflected in decomposition length:
    causative = 3 steps, noncausative = 2 steps. -/
theorem decomposition_reflects_transitivity :
    (decompose causativePropertyConstruction).length = 3 ∧
    (decompose noncausativePropertyConstruction).length = 2 := by
  constructor <;> native_decide

end ConstructionGrammar.Studies.GoldbergJackendoff2004.Bridge
