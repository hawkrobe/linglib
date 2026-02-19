import Linglib.Theories.Syntax.ConstructionGrammar.Studies.GoldbergJackendoff2004
import Linglib.Theories.Semantics.Causation.Sufficiency
import Linglib.Theories.Semantics.Causation.Necessity
import Linglib.Theories.Semantics.Lexical.Verb.ChangeOfState.Theory
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Theories.Semantics.Causation.ProductionDependence

/-!
# Resultatives as Concealed Causatives

Connects the resultative construction (Goldberg & Jackendoff 2004) to the
causative semantics infrastructure:

1. **Causal Dynamics**: causative resultatives modeled as concrete
   `CausalDynamics` with structural sufficiency proofs (Nadathur & Lauer 2020)
   and CC-selection constraints (Baglini & Bar-Asher Siegal 2025)
2. **Tightness via Causal Necessity**: Levin (2019) concealed causative
   constraint — intervening causers with independent energy sources
   disrupt necessity under counterfactual intervention, formalized
   through `completesForEffect` (not graph-structural checks)
3. **Thick/Thin Convergence**: three independent paths (Martin et al. 2025,
   G&J 2004, Embick 2009) converge on `.make`/`makeSem`
4. **Aspect**: resultative telicizes activity verbs via bounded RP
5. **ChangeOfState**: constructional BECOME maps to CoSType.inception
6. **Müller decomposability**: all subconstructions decompose into
   universal schemata

## References

- Goldberg, A. E. & Jackendoff, R. (2004). The English Resultative as a
  Family of Constructions. Language, 80(3), 532–568.
- Nadathur, P. & Lauer, S. (2020). Causal necessity, causal sufficiency,
  and the implications of causative verbs. Glossa.
- Baglini, R. & Bar-Asher Siegal, E. A. (2025). Modeling linguistic
  causation. Linguistics & Philosophy, 48, 647–691.
- Levin, B. (2019). Resultatives and constraints on concealed causatives.
  In Proceedings of JerSem.
- Martin, F., Rose, D. & Nichols, S. (2025). Burning facts: thick and thin
  causatives. Version 1, November 23, 2025.
-/

namespace Causative.Resultatives

open ConstructionGrammar
open ConstructionGrammar.Studies.GoldbergJackendoff2004
open Semantics.Lexical.Verb.Aspect
open Semantics.Lexical.Verb.ChangeOfState
open Core.Interfaces
open Core.Causation
open NadathurLauer2020.Sufficiency
open NadathurLauer2020.Necessity
open NadathurLauer2020.Builder (CausativeBuilder)
open Fragments.English.Predicates.Verbal (VerbEntry make cause)
open MartinRoseNichols2025

/-! ## Causal Dynamics (Nadathur & Lauer 2020; Baglini & Bar-Asher Siegal 2025)

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

/-! ### Causal models for causative resultatives

Each causative resultative maps to a concrete `CausalDynamics` where the
verbal subevent variable causally determines the result variable. -/

def hammeringVar : Variable := mkVar "hammering"
def flatVar : Variable := mkVar "flat"

/-- "She hammered the metal flat": hammering → flat. -/
def hammerFlatModel : CausalDynamics :=
  ⟨[CausalLaw.simple hammeringVar flatVar]⟩

def kickingVar : Variable := mkVar "kicking"
def inFieldVar : Variable := mkVar "in_field"

/-- "She kicked the ball into the field": kicking → in_field. -/
def kickIntoFieldModel : CausalDynamics :=
  ⟨[CausalLaw.simple kickingVar inFieldVar]⟩

def laughingVar : Variable := mkVar "laughing"
def sillyVar : Variable := mkVar "silly"

/-- "She laughed herself silly" (fake reflexive): laughing → silly. -/
def laughSillyModel : CausalDynamics :=
  ⟨[CausalLaw.simple laughingVar sillyVar]⟩

/-! ### Sufficiency proofs (N&L 2020 Def 23) -/

/-- Hammering is causally sufficient for flatness. -/
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

/-! ### Necessity proofs

Single-pathway resultatives: verbal subevent is both sufficient and necessary. -/

/-- Hammering is causally necessary for flatness. -/
theorem hammer_necessary_for_flat :
    let background := Situation.empty.extend hammeringVar true
    causallyNecessary hammerFlatModel background hammeringVar flatVar = true := by
  native_decide

/-- Both `makeSem` and `causeSem` hold for "hammer flat"
    (no overdetermination). -/
theorem hammer_flat_make_and_cause :
    let background := Situation.empty.extend hammeringVar true
    makeSem hammerFlatModel background hammeringVar flatVar = true ∧
    causeSem hammerFlatModel background hammeringVar flatVar = true := by
  constructor <;> native_decide

/-! ### Noncausative resultatives = empty dynamics

"The river froze solid": RESULT relation, no CAUSE. -/

def freezingVar : Variable := mkVar "freezing"
def solidVar : Variable := mkVar "solid"

/-- Noncausative resultatives have empty causal dynamics. -/
def freezeSolidModel : CausalDynamics := CausalDynamics.empty

/-- In the empty model, freezing is NOT sufficient for solidity. -/
theorem freeze_not_sufficient :
    causallySufficient freezeSolidModel Situation.empty freezingVar solidVar = false := by
  native_decide

/-- Causative → non-empty dynamics; noncausative → empty. -/
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

/-! ### Agreement with Boolean flags -/

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

/-! ### CC-selection (Baglini & Bar-Asher Siegal 2025)

Different causative constructions constrain which condition from a causal
model can be selected as "the cause." BBS2025 call this CC-selection.

- Overt "cause" (BBS2025, Formula 11): the subject must be an INUS member
  of a sufficient set — any contributing condition qualifies
- CoS/lexical causatives (BBS2025, Formula 14): the subject must be the
  **completion event** — the last condition to be realized, whose occurrence
  makes the result inevitable
- Resultatives pattern with CoS: the verbal subevent completes the
  sufficient set for the constructional result -/

/-- How a causative construction selects its cause (BBS2025). -/
inductive CCSelectionMode where
  /-- Overt "cause": subject is any member of a sufficient set (BBS2025 §4.1) -/
  | memberOfSufficientSet
  /-- CoS/resultative: subject completes a sufficient set (BBS2025 §4.2) -/
  | completionOfSufficientSet
  deriving Repr, DecidableEq, BEq

/-- Resultatives select via completion (like CoS verbs). -/
def resultativeCCSelection : CCSelectionMode := .completionOfSufficientSet

/-- BBS2025 completion event: sufficient + necessary in context. -/
def completesForEffect (dyn : CausalDynamics) (background : Situation)
    (cause effect : Variable) : Bool :=
  -- With cause: the set is sufficient
  causallySufficient dyn background cause effect &&
  -- Without cause: the set is NOT sufficient (cause is needed)
  causallyNecessary dyn (background.extend cause true) cause effect

/-- Hammering completes the sufficient set for flatness. -/
theorem hammer_completes_for_flat :
    completesForEffect hammerFlatModel Situation.empty hammeringVar flatVar = true := by
  native_decide

/-- Kicking completes the sufficient set for in-field. -/
theorem kick_completes_for_field :
    completesForEffect kickIntoFieldModel Situation.empty kickingVar inFieldVar = true := by
  native_decide

/-! ### Temporal constraint as completion event (G&J Principle 33) -/

/-- Causal completion + temporal ordering. -/
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

/-- Result preceding verbal subevent violates temporal constraint. -/
theorem hammer_not_completion_if_result_first :
    isCompletionEvent hammerFlatModel Situation.empty
      hammeringVar flatVar .constructionalFirst = false := by
  native_decide

/-! ### CausativeBuilder bridge -/

/-- The resultative construction uses `.make` (sufficiency). -/
def resultativeCausativeBuilder : CausativeBuilder := .make

/-- Resultative causation uses the `.make` builder. -/
theorem resultative_is_make :
    resultativeCausativeBuilder = .make := rfl

/-- Resultative CAUSE matches the Fragment entry for "make". -/
theorem resultative_cause_matches_make_verb :
    make.causativeBuilder = some resultativeCausativeBuilder := rfl

/-- Resultative CAUSE ≠ "cause" verb (`.make` ≠ `.cause`). -/
theorem resultative_cause_differs_from_cause_verb :
    cause.causativeBuilder ≠ some resultativeCausativeBuilder := by
  decide

/-- `.prevent` is incompatible with resultatives. -/
theorem prevent_incompatible_with_resultative :
    CausativeBuilder.prevent ≠ resultativeCausativeBuilder := by decide

/-! ## Levin's (2019) Tightness via Causal Necessity

Resultatives require tightness: no intervening causer with its own energy
source. Tightness ≡ `completesForEffect` (sufficiency + necessity). The
necessity component does the explanatory work: `causallyNecessary` runs
`normalDevelopment` with cause=false. An intermediate with an independent
energy source still fires without the cause, so necessity fails.

| Example | Chain | Indep. source? | `completesForEffect` |
|---------|-------|----------------|---------------------|
| "hammer metal flat" | direct | — | true |
| "drink teapot dry" | passive chain | No | true |
| "kick door open" (direct) | direct | — | true |
| *"kick door open" (via ball) | active chain | Yes | false |

`hasDirectLaw` (graph inspection) is insufficient: it rejects
"drink teapot dry" (passive chain, no direct law, but tight). -/

section Tightness

private def drinkingVar : Variable := mkVar "drinking"
private def teaRemovalVar : Variable := mkVar "tea_removal"
private def teapotDryVar : Variable := mkVar "teapot_dry"

/-- "Drink the teapot dry": passive chain (Levin §4).
    drinking → tea_removal → teapot_dry.
    Tea removal has no independent energy source. -/
def drinkTeapotDryModel : CausalDynamics :=
  CausalDynamics.causalChain drinkingVar teaRemovalVar teapotDryVar

private def kickingDoorVar : Variable := mkVar "kicking"
private def ballMotionVar : Variable := mkVar "ball_motion"
private def ballEnergyVar : Variable := mkVar "ball_energy"
private def doorOpenVar : Variable := mkVar "door_open"

/-- *"Kick the door open" via ball (UNAVAILABLE, Levin §7).
    kick → ball_motion → door_open, plus ball_energy → ball_motion.
    The ball has an independent energy source. -/
def kickDoorViaBallModel : CausalDynamics :=
  ⟨[ CausalLaw.simple kickingDoorVar ballMotionVar,
     CausalLaw.simple ballMotionVar doorOpenVar,
     CausalLaw.simple ballEnergyVar ballMotionVar ]⟩

/-- Background: ball has its own energy. -/
def ballHasEnergyBg : Situation :=
  Situation.empty.extend ballEnergyVar true

/-- "Kick the door open" (direct, available reading). kick → door_open. -/
def kickDoorDirectModel : CausalDynamics :=
  ⟨[CausalLaw.simple kickingDoorVar doorOpenVar]⟩

/-! ### Tightness = `completesForEffect`

Each theorem runs `normalDevelopment` under counterfactual intervention
(cause=true for sufficiency, cause=false for necessity). -/

theorem hammer_flat_tight :
    completesForEffect hammerFlatModel Situation.empty
      hammeringVar flatVar = true := by native_decide

/-- Tight despite being a chain: removing drinking leaves tea_removal
    undetermined (no independent source), so teapot_dry doesn't fire. -/
theorem drink_teapot_dry_tight :
    completesForEffect drinkTeapotDryModel Situation.empty
      drinkingVar teapotDryVar = true := by native_decide

/-- NOT tight: removing kicking still allows ball_energy → ball_motion
    → door_open. The kick is not necessary. -/
theorem kick_door_via_ball_not_tight :
    completesForEffect kickDoorViaBallModel ballHasEnergyBg
      kickingDoorVar doorOpenVar = false := by native_decide

theorem kick_door_direct_tight :
    completesForEffect kickDoorDirectModel Situation.empty
      kickingDoorVar doorOpenVar = true := by native_decide

/-- `hasDirectLaw` (graph inspection) incorrectly rejects the passive
    chain "drink teapot dry" — no direct law, but tight. -/
theorem drink_dry_no_direct_law_but_tight :
    hasDirectLaw drinkTeapotDryModel drinkingVar teapotDryVar = false ∧
    completesForEffect drinkTeapotDryModel Situation.empty
      drinkingVar teapotDryVar = true := by
  constructor <;> native_decide

/-! ### Intervening causer = independent source -/

/-- Ball has an independent source (ball_energy law). -/
theorem ball_has_independent_source :
    hasIndependentSource kickDoorViaBallModel
      kickingDoorVar ballMotionVar = true := by
  native_decide

/-- Tea removal has no independent source. -/
theorem tea_no_independent_source :
    hasIndependentSource drinkTeapotDryModel
      drinkingVar teaRemovalVar = false := by
  native_decide

set_option maxHeartbeats 800000 in
/-- For a chain a → b → c, an active independent source for b disrupts
    `completesForEffect` for a → c. The independent source fires b
    even with a=false, so a is not necessary. -/
theorem independent_source_disrupts_tightness
    (cause intermediate effect indepSrc : Variable)
    (hci : cause ≠ intermediate) (hce : cause ≠ effect)
    (hie : intermediate ≠ effect)
    (hsc : indepSrc ≠ cause) (hsi : indepSrc ≠ intermediate)
    (hse : indepSrc ≠ effect) :
    let chain := CausalDynamics.causalChain cause intermediate effect
    completesForEffect chain Situation.empty cause effect = true →
    let withIndep : CausalDynamics :=
      ⟨[CausalLaw.simple cause intermediate,
        CausalLaw.simple intermediate effect,
        CausalLaw.simple indepSrc intermediate]⟩
    let bg := Situation.empty.extend indepSrc true
    completesForEffect withIndep bg cause effect = false := by
  intro chain _ withIndep bg
  -- Necessity fails: indepSrc → intermediate → effect fires even without cause
  simp only [completesForEffect, Bool.and_eq_false_iff]
  right; unfold causallyNecessary; dsimp only
  suffices h : (normalDevelopment withIndep
      ((bg.extend cause true).extend cause false)).hasValue effect true = true by
    rw [h]; rfl
  set s := (bg.extend cause true).extend cause false
  -- HasValue facts for s (counterfactual situation with cause=false)
  have hs_c : s.hasValue cause true = false := by simp [s, bg]
  have hs_i : s.hasValue intermediate true = false := by
    simp only [s, bg, Situation.hasValue, Situation.extend, Situation.empty]
    split_ifs <;> simp_all [Ne.symm hci, Ne.symm hsi]
  have hs_d : s.hasValue indepSrc true = true := by simp [s, bg, hsc]
  have hs_e : s.hasValue effect true = false := by
    simp only [s, bg, Situation.hasValue, Situation.extend, Situation.empty]
    split_ifs <;> simp_all [Ne.symm hce, Ne.symm hse]
  -- Round 1: only indepSrc→intermediate fires (cause=false, intermediate=false)
  have hp1 : (CausalLaw.simple cause intermediate).preconditionsMet s = false := by
    simp [CausalLaw.preconditionsMet, CausalLaw.simple, hs_c]
  have hp2 : (CausalLaw.simple intermediate effect).preconditionsMet s = false := by
    simp [CausalLaw.preconditionsMet, CausalLaw.simple, hs_i]
  have hp3 : (CausalLaw.simple indepSrc intermediate).preconditionsMet s = true := by
    simp [CausalLaw.preconditionsMet, CausalLaw.simple, hs_d]
  have hround1 : applyLawsOnce withIndep s = s.extend intermediate true := by
    simp only [applyLawsOnce, withIndep, List.foldl_cons, List.foldl_nil]
    rw [CausalLaw.apply_of_not_met hp1, CausalLaw.apply_of_not_met hp2,
        CausalLaw.apply_of_met hp3]
    simp [CausalLaw.simple]
  -- HasValue facts for s1 := s.extend intermediate true
  have hs1_i : (s.extend intermediate true).hasValue intermediate true = true := by
    simp [Situation.extend_hasValue_same]
  have hs1_c : (s.extend intermediate true).hasValue cause true = false := by
    rw [Situation.extend_hasValue_diff s intermediate cause true true hci]; exact hs_c
  have hs1_d : (s.extend intermediate true).hasValue indepSrc true = true := by
    rw [Situation.extend_hasValue_diff s intermediate indepSrc true true hsi]; exact hs_d
  have hs1_e : (s.extend intermediate true).hasValue effect true = false := by
    rw [Situation.extend_hasValue_diff s intermediate effect true true (Ne.symm hie)]
    exact hs_e
  -- Not fixpoint after round 1 (intermediate→effect can fire)
  have hnfix : isFixpoint withIndep (applyLawsOnce withIndep s) = false := by
    rw [hround1]
    simp only [isFixpoint, withIndep, List.all_cons, List.all_nil, Bool.and_true,
      CausalLaw.preconditionsMet, CausalLaw.simple,
      List.all_cons, List.all_nil, Bool.and_true,
      hs1_c, hs1_i, hs1_d, hs1_e]; decide
  -- Round 2: intermediate→effect fires, indepSrc→intermediate is redundant
  have hp2_1 : (CausalLaw.simple cause intermediate).preconditionsMet
      (s.extend intermediate true) = false := by
    simp [CausalLaw.preconditionsMet, CausalLaw.simple, hs1_c]
  have hp2_2 : (CausalLaw.simple intermediate effect).preconditionsMet
      (s.extend intermediate true) = true := by
    simp [CausalLaw.preconditionsMet, CausalLaw.simple, hs1_i]
  have hs1e_d : ((s.extend intermediate true).extend effect true).hasValue
      indepSrc true = true := by
    rw [Situation.extend_hasValue_diff (s.extend intermediate true) effect indepSrc
        true true hse]
    exact hs1_d
  have hp2_3 : (CausalLaw.simple indepSrc intermediate).preconditionsMet
      ((s.extend intermediate true).extend effect true) = true := by
    simp [CausalLaw.preconditionsMet, CausalLaw.simple, hs1e_d]
  have hround2 : applyLawsOnce withIndep (s.extend intermediate true) =
      ((s.extend intermediate true).extend effect true).extend intermediate true := by
    simp only [applyLawsOnce, withIndep, List.foldl_cons, List.foldl_nil]
    rw [CausalLaw.apply_of_not_met hp2_1, CausalLaw.apply_of_met hp2_2]
    simp only [CausalLaw.simple_effect, CausalLaw.simple_effectValue]
    rw [CausalLaw.apply_of_met hp2_3]
    simp [CausalLaw.simple]
  -- HasValue facts for s2 (fixpoint situation)
  have hs2_i : (((s.extend intermediate true).extend effect true).extend
      intermediate true).hasValue intermediate true = true := by
    simp [Situation.extend_hasValue_same]
  have hs2_e : (((s.extend intermediate true).extend effect true).extend
      intermediate true).hasValue effect true = true := by
    rw [Situation.extend_hasValue_diff ((s.extend intermediate true).extend effect true)
        intermediate effect true true (Ne.symm hie)]
    simp [Situation.extend_hasValue_same]
  have hs2_c : (((s.extend intermediate true).extend effect true).extend
      intermediate true).hasValue cause true = false := by
    rw [Situation.extend_hasValue_diff ((s.extend intermediate true).extend effect true)
        intermediate cause true true hci,
      Situation.extend_hasValue_diff (s.extend intermediate true) effect cause true true hce]
    exact hs1_c
  have hs2_d : (((s.extend intermediate true).extend effect true).extend
      intermediate true).hasValue indepSrc true = true := by
    rw [Situation.extend_hasValue_diff ((s.extend intermediate true).extend effect true)
        intermediate indepSrc true true hsi,
      Situation.extend_hasValue_diff (s.extend intermediate true) effect indepSrc
        true true hse]
    exact hs1_d
  -- IS fixpoint after round 2 (all effects already set)
  have hfix : isFixpoint withIndep (applyLawsOnce withIndep
      (applyLawsOnce withIndep s)) = true := by
    rw [hround1, hround2]
    simp only [isFixpoint, withIndep, List.all_cons, List.all_nil, Bool.and_true,
      CausalLaw.preconditionsMet, CausalLaw.simple,
      List.all_cons, List.all_nil, Bool.and_true,
      hs2_c, hs2_i, hs2_d, hs2_e]; decide
  -- normalDevelopment reaches round 2 result; effect is true
  change (normalDevelopment withIndep s 100).hasValue effect true = true
  rw [show (100 : Nat) = 98 + 2 from rfl,
      normalDevelopment_fixpoint_after_two _ _ hnfix hfix,
      hround1, hround2]
  exact hs2_e

/-- Concrete witness: passive chain tight, active chain not tight. -/
theorem independent_source_disrupts_tightness_concrete :
    completesForEffect drinkTeapotDryModel Situation.empty
      drinkingVar teapotDryVar = true ∧
    completesForEffect kickDoorViaBallModel ballHasEnergyBg
      kickingDoorVar doorOpenVar = false := by
  constructor <;> native_decide

/-! ### Contiguity (Levin §4)

Nonselected-NP resultatives require contiguity between verb's object
and affected entity. All types involve passive intermediates (no
independent source), so `completesForEffect` holds. -/

/-- Spatial contiguity preserving tightness in nonselected NP resultatives. -/
inductive ContiguityType where
  | containerContents  -- "drink teapot dry", "cry eyes out"
  | contentsContainer  -- "fill bucket full", "load truck full"
  | impingement        -- "wipe table clean", "scrub floor clean"
  deriving DecidableEq, Repr, BEq

/-- All contiguity types involve passive intermediates (no independent
    energy source), so necessity propagates through the chain. -/
def ContiguityType.intermediateIsPassive : ContiguityType → Bool
  | .containerContents => true
  | .contentsContainer => true
  | .impingement => true

end Tightness

/-! ## Three-Way Convergence: Thick ↔ P-CAUSE ↔ Resultative

Three independently-defined modules converge on the same prediction:

1. **ProductionDependence.lean**: Thick manner → P-CAUSE → `.make` builder
2. **Resultatives.lean**: Resultative CAUSE → `.make` builder
3. **ThickThin.lean**: Thick manner → ASR-compatible (empirical data)

This convergence is non-trivial: each path was formalized independently
following different papers (Martin et al. 2025, G&J 2004, Embick 2009).
The fact that they agree validates the cross-module architecture. -/

/-- Three independent paths converge on `.make`. -/
theorem thick_manner_resultative_convergence :
    -- Path 1: Thick manner → production constraint → P-CAUSE
    productionConstraint .thickManner = .production ∧
    -- Path 2: P-CAUSE → analogous builder → .make
    CausationType.production.analogousBuilder = .make ∧
    -- Path 3: Resultative construction → .make
    resultativeCausativeBuilder = .make ∧
    -- Convergence: Path 1+2 meets Path 3
    CausationType.production.analogousBuilder = resultativeCausativeBuilder :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- Thin → `.cause` ≠ resultative `.make` (*kill open). -/
theorem thin_incompatible_with_resultative_cause :
    productionConstraint .thin = .dependence ∧
    CausationType.dependence.analogousBuilder = .cause ∧
    CausativeBuilder.cause ≠ resultativeCausativeBuilder := by
  exact ⟨rfl, rfl, by decide⟩

/-! ## Aspect: activity + bounded RP → accomplishment -/

/-- Bounded RP telicizes activity (reuses `telicize_activity`). -/
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

/-! ## ChangeOfState: BECOME = inception (¬P → P) -/

/-- Constructional BECOME = CoS inception. -/
def resultStateMapsToCoS : CoSType := .inception

/-- All resultative entries have BECOME. -/
theorem all_have_become :
    allEntries.all (·.subevents.constructional.hasBecome) = true := by
  native_decide

/-- Inception presupposes ¬P before. -/
theorem inception_presupposes_not_prior {W : Type*} (P : W → Bool) (w : W) :
    priorStatePresup .inception P w = !P w := rfl

/-- Inception asserts P after. -/
theorem inception_asserts_result {W : Type*} (P : W → Bool) :
    resultStateAssertion .inception P = P := rfl

/-! ## Müller Decomposability

All four resultative subconstructions are fully abstract and therefore
decomposable into Müller's universal schemata.

Causative subconstructions → [HS, HC, HC] (same as parent resultative)
Noncausative subconstructions → [HS, HC] (intransitive, fewer complements) -/

/-- All four subconstructions are decomposable. -/
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

end Causative.Resultatives
