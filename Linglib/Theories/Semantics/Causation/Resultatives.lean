import Linglib.Theories.Syntax.ConstructionGrammar.Studies.GoldbergJackendoff2004
import Linglib.Theories.Semantics.Causation.CCSelection
import Linglib.Theories.Semantics.Causation.Sufficiency
import Linglib.Theories.Semantics.Causation.Necessity
import Linglib.Theories.Semantics.Verb.ChangeOfState.Theory
import Linglib.Theories.Semantics.Causation.ProductionDependence

/-!
# Resultatives as Concealed Causatives
@cite{baglini-bar-asher-siegal-2025} @cite{goldberg-jackendoff-2004} @cite{levin-2019} @cite{martin-rose-nichols-2025} @cite{nadathur-lauer-2020}

Connects the resultative construction to the
causative semantics infrastructure:

1. **Causal Dynamics**: causative resultatives modeled as concrete
   `CausalDynamics` with structural sufficiency proofs
   and CC-selection constraints (Baglini & Bar-Asher @cite{baglini-bar-asher-siegal-2025})
2. **Tightness via Causal Necessity**: @cite{levin-2019} concealed causative
   constraint — intervening causers with independent energy sources
   disrupt necessity under counterfactual intervention, formalized
   through `completesForEffect` (not graph-structural checks)
3. **Thick/Thin Convergence**: three independent paths (@cite{martin-rose-nichols-2025},
   @cite{goldberg-jackendoff-2004}, @cite{embick-2009}) converge on `.make`/`makeSem`
4. **Aspect**: resultative telicizes activity verbs via bounded RP
5. **ChangeOfState**: constructional BECOME maps to CoSType.inception
6. **Müller decomposability**: all subconstructions decompose into
   universal schemata

-/

namespace Semantics.Causation.Resultatives

open ConstructionGrammar
open ConstructionGrammar.Studies.GoldbergJackendoff2004
open Semantics.Tense.Aspect.LexicalAspect
open Core.Verbs
open Semantics.Verb.ChangeOfState
open Core
open Core.Causal
open Semantics.Causation.Sufficiency
open Semantics.Causation.Necessity
open Core.Verbs (Causative)
open Semantics.Causation.ProductionDependence
open Semantics.Causation.CCSelection

/-! ## Causal Dynamics (@cite{nadathur-lauer-2020}; Baglini & Bar-Asher @cite{baglini-bar-asher-siegal-2025})

The constructional CAUSE in causative resultatives maps to @cite{nadathur-lauer-2020} causal sufficiency: the verbal subevent is sufficient for the
constructional result. We build concrete `CausalDynamics` and prove
structural sufficiency/necessity results.

### CC-selection (Baglini & Bar-Asher @cite{baglini-bar-asher-siegal-2025})

The resultative construction performs **CC-selection**: it constrains which
condition from a causal model can fill the cause role. Causative resultatives
select via completion of a sufficient set: the verbal subevent must be the
final condition that makes the result inevitable. Combined with the temporal
constraint (G&J temporal ordering), this gives the @cite{baglini-bar-asher-siegal-2025} completion event
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

/-! ### Sufficiency proofs (@cite{nadathur-lauer-2020} Def 23) -/

/-- Hammering is causally sufficient for flatness. -/
theorem hammer_sufficient_for_flat :
    causallySufficient hammerFlatModel Situation.empty hammeringVar flatVar := by
  native_decide

/-- Kicking is causally sufficient for being in the field. -/
theorem kick_sufficient_for_field :
    causallySufficient kickIntoFieldModel Situation.empty kickingVar inFieldVar := by
  native_decide

/-- Laughing is causally sufficient for becoming silly (fake reflexive). -/
theorem laugh_sufficient_for_silly :
    causallySufficient laughSillyModel Situation.empty laughingVar sillyVar := by
  native_decide

/-! ### Necessity proofs

Single-pathway resultatives: verbal subevent is both sufficient and necessary. -/

/-- Hammering is causally necessary for flatness.
    Under @cite{nadathur-2024} Def 10b, the background must NOT
    include the cause (precondition rejects it). -/
theorem hammer_necessary_for_flat :
    causallyNecessary hammerFlatModel Situation.empty hammeringVar flatVar := by
  native_decide

/-- Both `makeSem` and `causeSem` hold for "hammer flat"
    (no overdetermination). -/
theorem hammer_flat_make_and_cause :
    makeSem hammerFlatModel Situation.empty hammeringVar flatVar ∧
    causeSem hammerFlatModel Situation.empty hammeringVar flatVar := by
  constructor <;> native_decide

/-! ### Noncausative resultatives = empty dynamics

"The river froze solid": RESULT relation, no CAUSE. -/

def freezingVar : Variable := mkVar "freezing"
def solidVar : Variable := mkVar "solid"

/-- Noncausative resultatives have empty causal dynamics. -/
def freezeSolidModel : CausalDynamics := CausalDynamics.empty

/-- In the empty model, freezing is NOT sufficient for solidity. -/
theorem freeze_not_sufficient :
    ¬ (causallySufficient freezeSolidModel Situation.empty freezingVar solidVar) := by
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

/-- isCausative ↔ hasCause — derived from the subconstruction, not stipulated per entry. -/
theorem causative_iff_has_cause (sc : ResultativeSubconstruction) :
    sc.isCausative = sc.constructionalDesc.hasCause := by
  cases sc <;> rfl

/-- All causative entries in the data have CAUSE (via derived subevent). -/
theorem causativeResultativeHasCAUSE :
    (allEntries.filter (·.subconstruction.isCausative)).all
      (·.dualSubevent.constructional.hasCause) = true := by
  native_decide

/-- MEANS-relation causative entries all have CAUSE. -/
theorem causative_means_have_cause :
    (allEntries.filter (λ e =>
      e.subconstruction.isCausative && e.subeventRelation == .means
    )).all (·.dualSubevent.constructional.hasCause) = true := by
  native_decide

/-! ### CC-selection (Baglini & Bar-Asher @cite{baglini-bar-asher-siegal-2025})

CC-selection types (`CCSelectionMode`, `completesForEffect`) are defined in
`Semantics.Causation.CCSelection` and re-exported here for backward compatibility.

- Overt "cause": `memberOfSufficientSet` — any necessary condition
- CoS/resultative: `completionOfSufficientSet` — the completing condition -/

export Semantics.Causation.CCSelection (CCSelectionMode completesForEffect ccConstraintSatisfied)

/-- Resultatives select via completion (like CoS verbs). -/
def resultativeCCSelection : CCSelectionMode := .completionOfSufficientSet

/-- Hammering completes the sufficient set for flatness. -/
theorem hammer_completes_for_flat :
    completesForEffect hammerFlatModel Situation.empty hammeringVar flatVar = true := by
  native_decide

/-- Kicking completes the sufficient set for in-field. -/
theorem kick_completes_for_field :
    completesForEffect kickIntoFieldModel Situation.empty kickingVar inFieldVar = true := by
  native_decide

/-! ### Temporal constraint as completion event

The temporal constraint is now relation-dependent: for MEANS relations,
the constructional subevent cannot precede the verbal subevent. -/

/-- Causal completion + temporal ordering (relation-dependent). -/
def isCompletionEvent (dyn : CausalDynamics) (background : Situation)
    (cause effect : Variable) (rel : SubeventRelation) (order : TemporalOrder) : Bool :=
  completesForEffect dyn background cause effect &&
  temporalConstraintSatisfied rel order

/-- Hammering is a completion event for flatness (verbal precedes result). -/
theorem hammer_is_completion_event :
    isCompletionEvent hammerFlatModel Situation.empty
      hammeringVar flatVar .means .verbalFirst = true := by
  native_decide

/-- Hammering is a completion event when simultaneous with result. -/
theorem hammer_completion_simultaneous :
    isCompletionEvent hammerFlatModel Situation.empty
      hammeringVar flatVar .means .simultaneous = true := by
  native_decide

/-- MEANS relation: constructional-first violates temporal constraint. -/
theorem hammer_not_completion_if_result_first :
    isCompletionEvent hammerFlatModel Situation.empty
      hammeringVar flatVar .means .constructionalFirst = false := by
  native_decide

/-! ### Causative bridge: derived from SubeventRelation + CAUSE

The resultative's Causative is `.make`, but this is NOT stipulated —
it is DERIVED from two independently-motivated properties:

1. **MEANS relation**: the verbal subevent is the means by which the
   constructional subevent is brought about (@cite{goldberg-jackendoff-2004}).
   MEANS ↔ causal sufficiency: adding the verbal subevent guarantees
   the result.

2. **CAUSE in constructional subevent**: causative subconstructions have
   `hasCause = true` (derived from `constructionalDesc`).

MEANS + CAUSE → `makeSem` (sufficiency). Among sufficiency builders,
`.make` is uniquely identified by lacking coercion (`.force`) and
barrier-removal (`.enable`). -/

/-- Derive the Causative from subevent relation + constructional desc
    + force-dynamic properties.

    **Step 1** (structural): MEANS + CAUSE licenses a sufficiency-based builder.
    All other combinations don't license an independent causal builder:
    - RESULT: verbal subevent is caused BY the result (reversed directionality)
    - INSTANCE: verbal subevent IS the constructional subevent (identity, not causation)
    - CO-OCCURRENCE: no causal connection
    - ¬hasCause: noncausative (BECOME without CAUSE) — no external causation

    **Step 2** (force-dynamic): among sufficiency builders, force-dynamic
    properties disambiguate:
    - coercive → `.force` (overcome resistance: "force X into Y")
    - permissive → `.enable` (barrier removal: "let X go free")
    - neutral → `.make` (default: resultatives, "make X flat")

    Necessity (`.cause`) and blocking (`.prevent`) require causal model
    inspection — they cannot be derived from subevent structure alone. -/
def deriveCausativeBuilder (rel : SubeventRelation) (desc : SubeventDesc)
    (coercive : Bool := false) (permissive : Bool := false) :
    Option Causative :=
  match rel, desc.hasCause with
  | .means, true =>
    some (if coercive then .force
          else if permissive then .enable
          else .make)
  | _, _ => none

/-- `.make` is the unique builder asserting neutral sufficiency
    (no coercion, no barrier-removal). -/
theorem make_unique_neutral_sufficiency (b : Causative)
    (hs : b.assertsSufficiency = true)
    (hc : b.isCoercive = false)
    (hp : b.isPermissive = false) :
    b = .make := by
  cases b <;> simp_all [Causative.assertsSufficiency,
    Causative.isCoercive, Causative.isPermissive]

/-- Neutral derivation (no coercion, no permissivity) yields `.make`. -/
theorem neutral_derives_make (desc : SubeventDesc)
    (h : desc.hasCause = true) :
    deriveCausativeBuilder .means desc = some .make := by
  simp [deriveCausativeBuilder, h]

/-- Coercive derivation yields `.force`. -/
theorem coercive_derives_force (desc : SubeventDesc)
    (h : desc.hasCause = true) :
    deriveCausativeBuilder .means desc (coercive := true) = some .force := by
  simp [deriveCausativeBuilder, h]

/-- Permissive derivation yields `.enable`. -/
theorem permissive_derives_enable (desc : SubeventDesc)
    (h : desc.hasCause = true) :
    deriveCausativeBuilder .means desc (permissive := true) = some .enable := by
  simp [deriveCausativeBuilder, h]

/-- Coercive takes priority over permissive (force > enable). -/
theorem coercive_overrides_permissive (desc : SubeventDesc)
    (h : desc.hasCause = true) :
    deriveCausativeBuilder .means desc (coercive := true) (permissive := true) =
      some .force := by
  simp [deriveCausativeBuilder, h]

/-- For any causative subconstruction with MEANS relation,
    the derived builder is `.make` (resultatives are neutral — no
    coercion, no barrier-removal). -/
theorem causative_means_derives_make (sc : ResultativeSubconstruction)
    (h : sc.isCausative = true) :
    deriveCausativeBuilder .means sc.constructionalDesc = some .make := by
  cases sc <;> simp [ResultativeSubconstruction.isCausative] at h <;>
    simp [deriveCausativeBuilder, ResultativeSubconstruction.constructionalDesc]

/-- Noncausative subconstructions don't derive a Causative
    (no CAUSE operator → no external causation to encode). -/
theorem noncausative_no_builder (sc : ResultativeSubconstruction)
    (h : sc.isCausative = false)
    (coercive permissive : Bool) :
    deriveCausativeBuilder .means sc.constructionalDesc coercive permissive = none := by
  cases sc <;> simp [ResultativeSubconstruction.isCausative] at h <;>
    simp [deriveCausativeBuilder, ResultativeSubconstruction.constructionalDesc]

/-- Non-MEANS relations never derive a Causative, regardless of
    whether the constructional subevent has CAUSE or force-dynamic properties. -/
theorem non_means_no_builder (desc : SubeventDesc) (coercive permissive : Bool) :
    deriveCausativeBuilder .result desc coercive permissive = none ∧
    deriveCausativeBuilder .instance_ desc coercive permissive = none ∧
    deriveCausativeBuilder .coOccurrence desc coercive permissive = none := by
  simp [deriveCausativeBuilder]

/-- When `deriveCausativeBuilder` succeeds, the resulting builder
    asserts causal sufficiency — regardless of force-dynamic properties. -/
theorem derived_asserts_sufficiency (rel : SubeventRelation) (desc : SubeventDesc)
    (coercive permissive : Bool)
    (b : Causative) (h : deriveCausativeBuilder rel desc coercive permissive = some b) :
    b.assertsSufficiency = true := by
  unfold deriveCausativeBuilder at h
  split at h
  · simp only [Option.some.injEq] at h
    cases coercive <;> cases permissive <;>
      simp_all <;> subst h <;> rfl
  · simp at h

/-- The resultative Causative, derived from MEANS + CAUSE.
    Resultatives are neutral (no coercion, no barrier-removal), so
    the force-dynamic parameters default to false.
    `causative_means_derives_make` proves all causative subconstructions
    yield the same result. -/
def resultativeCausativeBuilder : Causative :=
  match deriveCausativeBuilder .means
    ResultativeSubconstruction.causativeProperty.constructionalDesc with
  | some b => b
  | none => .cause  -- unreachable: causativeProperty has hasCause = true

/-- The derived builder is `.make` — causal sufficiency without
    coercion or barrier-removal. -/
theorem resultative_is_make :
    resultativeCausativeBuilder = .make := rfl

/-- `.prevent` is incompatible with resultatives. -/
theorem prevent_incompatible_with_resultative :
    Causative.prevent ≠ resultativeCausativeBuilder := by decide

/-! ## @cite{levin-2019}'s Tightness via Causal Necessity

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

/-- "Drink the teapot dry": passive chain (@cite{levin-2019}).
    drinking → tea_removal → teapot_dry.
    Tea removal has no independent energy source. -/
def drinkTeapotDryModel : CausalDynamics :=
  CausalDynamics.causalChain drinkingVar teaRemovalVar teapotDryVar

private def kickingDoorVar : Variable := mkVar "kicking"
private def ballMotionVar : Variable := mkVar "ball_motion"
private def ballEnergyVar : Variable := mkVar "ball_energy"
private def doorOpenVar : Variable := mkVar "door_open"

/-- *"Kick the door open" via ball (UNAVAILABLE, @cite{levin-2019}).
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
    ¬ (hasDirectLaw drinkTeapotDryModel drinkingVar teapotDryVar) ∧
    completesForEffect drinkTeapotDryModel Situation.empty
      drinkingVar teapotDryVar = true := by
  constructor <;> native_decide

/-! ### Intervening causer = independent source -/

/-- Ball has an independent source (ball_energy law). -/
theorem ball_has_independent_source :
    hasIndependentSource kickDoorViaBallModel
      kickingDoorVar ballMotionVar := by
  native_decide

/-- Tea removal has no independent source. -/
theorem tea_no_independent_source :
    ¬ hasIndependentSource drinkTeapotDryModel
      drinkingVar teaRemovalVar := by
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
    completesForEffect chain Situation.empty cause effect →
    let withIndep : CausalDynamics :=
      ⟨[CausalLaw.simple cause intermediate,
        CausalLaw.simple intermediate effect,
        CausalLaw.simple indepSrc intermediate]⟩
    let bg := Situation.empty.extend indepSrc true
    ¬ completesForEffect withIndep bg cause effect := by
  intro _ _ withIndep bg ⟨_hSuf, hNotBut⟩
  -- Show but-for fails: effect develops in `bg.extend cause false`
  apply hNotBut
  set s := bg.extend cause false with hs
  -- Useful facts about s
  have hCauseFalse : s.hasValue cause false := by
    show s.valuation cause = some false; simp [hs, Situation.extend]
  have hIndepTrue : s.hasValue indepSrc true := by
    show s.valuation indepSrc = some true
    simp only [hs, bg, Situation.extend]
    rw [show (indepSrc == cause) = false from beq_false_of_ne hsc]
    show (Situation.empty.extend indepSrc true).valuation indepSrc = some true
    simp [Situation.extend]
  have hIntNone : s.get intermediate = none := by
    show ((Situation.empty.extend indepSrc true).extend cause false).get intermediate = none
    rw [Situation.extend_get_ne (Ne.symm hci),
        Situation.extend_get_ne (Ne.symm hsi)]; rfl
  have hEffNone : s.get effect = none := by
    show ((Situation.empty.extend indepSrc true).extend cause false).get effect = none
    rw [Situation.extend_get_ne (Ne.symm hce),
        Situation.extend_get_ne (Ne.symm hse)]; rfl
  -- Round 1: cause→int and int→eff don't fire (cause=false, int=none); indepSrc→int fires
  have hMetCI : ¬ (CausalLaw.simple cause intermediate).preconditionsMet s := by
    intro h
    have := h (cause, true) (by simp [CausalLaw.simple])
    unfold Situation.hasValue at this hCauseFalse
    rw [hCauseFalse] at this; cases this
  have hMetIE : ¬ (CausalLaw.simple intermediate effect).preconditionsMet s := by
    intro h
    have := h (intermediate, true) (by simp [CausalLaw.simple])
    unfold Situation.hasValue at this
    rw [show s.valuation intermediate = s.get intermediate from rfl, hIntNone] at this
    cases this
  have hMetSI : (CausalLaw.simple indepSrc intermediate).preconditionsMet s := by
    intro p hp; simp only [CausalLaw.simple, List.mem_singleton] at hp
    rw [hp]; exact hIndepTrue
  have hStep1_a : (CausalLaw.simple cause intermediate).apply s = s :=
    CausalLaw.apply_of_not_met hMetCI
  have hStep1_b : (CausalLaw.simple intermediate effect).apply s = s :=
    CausalLaw.apply_of_not_met hMetIE
  have hStep1_c : (CausalLaw.simple indepSrc intermediate).apply s
                  = s.extend intermediate true :=
    CausalLaw.apply_of_met_undetermined hMetSI hIntNone
  set s1 := s.extend intermediate true with hs1
  have hRound1 : applyLawsOnce withIndep s = s1 := by
    show ([_, _, _].foldl _ s) = _
    simp only [List.foldl_cons, List.foldl_nil]
    rw [hStep1_a, hStep1_b, hStep1_c]
  -- Round 2 setup: facts about s1
  have hCauseFalse1 : s1.hasValue cause false := by
    rw [hs1]; show (s.extend intermediate true).valuation cause = some false
    rw [show (s.extend intermediate true).valuation cause
          = (s.extend intermediate true).get cause from rfl,
        Situation.extend_get_ne hci]; exact hCauseFalse
  have hIntTrue1 : s1.hasValue intermediate true := by
    rw [hs1]; show (s.extend intermediate true).valuation intermediate = some true
    rw [show (s.extend intermediate true).valuation intermediate
          = (s.extend intermediate true).get intermediate from rfl,
        Situation.extend_get_same]
  have hEffNone1 : s1.get effect = none := by
    rw [hs1, Situation.extend_get_ne (Ne.symm hie)]; exact hEffNone
  -- Round 2: cause→int doesn't fire (cause=false); int→eff fires (int=true, eff=none);
  --          indepSrc→int doesn't fire (int already determined)
  have hMetCI' : ¬ (CausalLaw.simple cause intermediate).preconditionsMet s1 := by
    intro h
    have := h (cause, true) (by simp [CausalLaw.simple])
    unfold Situation.hasValue at this hCauseFalse1
    rw [hCauseFalse1] at this; cases this
  have hMetIE' : (CausalLaw.simple intermediate effect).preconditionsMet s1 := by
    intro p hp; simp only [CausalLaw.simple, List.mem_singleton] at hp
    rw [hp]; exact hIntTrue1
  have hStep2_a : (CausalLaw.simple cause intermediate).apply s1 = s1 :=
    CausalLaw.apply_of_not_met hMetCI'
  have hStep2_b : (CausalLaw.simple intermediate effect).apply s1
                  = s1.extend effect true :=
    CausalLaw.apply_of_met_undetermined hMetIE' hEffNone1
  have hStep2_c : (CausalLaw.simple indepSrc intermediate).apply (s1.extend effect true)
                  = s1.extend effect true := by
    apply CausalLaw.apply_of_determined
    show (s1.extend effect true).get intermediate = some true
    rw [Situation.extend_get_ne hie]
    rw [hs1, Situation.extend_get_same]
  set s2 := s1.extend effect true with hs2
  have hRound2 : applyLawsOnce withIndep s1 = s2 := by
    show ([_, _, _].foldl _ s1) = _
    simp only [List.foldl_cons, List.foldl_nil]
    rw [hStep2_a, hStep2_b, hStep2_c]
  -- s2 is a fixpoint
  have hFix : isFixpoint withIndep s2 := by
    intro law hLaw hMet hNone
    -- Three cases on which law
    have hLawMem : law ∈ [CausalLaw.simple cause intermediate,
                          CausalLaw.simple intermediate effect,
                          CausalLaw.simple indepSrc intermediate] := hLaw
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hLawMem
    -- s2 has cause=false and effect, intermediate determined; pre-compute s2 facts
    have hS2GetCause : s2.get cause = some false := by
      rw [hs2, hs1, Situation.extend_get_ne hce, Situation.extend_get_ne hci]
      show s.get cause = some false
      rw [hs]; show ((Situation.empty.extend indepSrc true).extend cause false).get cause = _
      rw [Situation.extend_get_same]
    have hS2GetEffect : s2.get effect = some true := by
      rw [hs2, Situation.extend_get_same]
    have hS2GetInt : s2.get intermediate = some true := by
      rw [hs2, Situation.extend_get_ne hie, hs1, Situation.extend_get_same]
    rcases hLawMem with hL | hL | hL
    · -- cause → int: cause is some false in s2, but precondition needs (cause, true)
      subst hL
      have := hMet (cause, true) (by simp [CausalLaw.simple])
      unfold Situation.hasValue at this
      rw [show s2.valuation cause = s2.get cause from rfl, hS2GetCause] at this
      cases this
    · -- int → eff: effect already determined in s2
      subst hL
      change s2.get effect = none at hNone
      rw [hS2GetEffect] at hNone; cases hNone
    · -- indepSrc → int: int already determined in s2
      subst hL
      change s2.get intermediate = none at hNone
      rw [hS2GetInt] at hNone; cases hNone
  -- Now chain the unfolds: s → s1 → s2 (fixpoint)
  have hNotFix_s : ¬ isFixpoint withIndep s := by
    intro hF; exact (hF (CausalLaw.simple indepSrc intermediate)
      (by simp [withIndep]) hMetSI) hIntNone
  have hNotFix_s1 : ¬ isFixpoint withIndep s1 := by
    intro hF; exact (hF (CausalLaw.simple intermediate effect)
      (by simp [withIndep]) hMetIE') hEffNone1
  rw [normalDevelopment_of_not_fixpoint hNotFix_s, hRound1]
  rw [normalDevelopment_of_not_fixpoint hNotFix_s1, hRound2]
  rw [normalDevelopment_of_fixpoint hFix]
  show s2.hasValue effect true
  rw [hs2]; show (s1.extend effect true).hasValue effect true
  rw [Situation.extend_hasValue_same]

/-- Concrete witness: passive chain tight, active chain not tight. -/
theorem independent_source_disrupts_tightness_concrete :
    completesForEffect drinkTeapotDryModel Situation.empty
      drinkingVar teapotDryVar ∧
    ¬ completesForEffect kickDoorViaBallModel ballHasEnergyBg
      kickingDoorVar doorOpenVar := by
  constructor <;> native_decide

/-! ### Contiguity (@cite{levin-2019})

Nonselected-NP resultatives require contiguity between verb's object
and affected entity. All types involve passive intermediates (no
independent source), so `completesForEffect` holds. -/

/-- Spatial contiguity preserving tightness in nonselected NP resultatives. -/
inductive ContiguityType where
  | containerContents  -- "drink teapot dry", "cry eyes out"
  | contentsContainer  -- "fill bucket full", "load truck full"
  | impingement        -- "wipe table clean", "scrub floor clean"
  deriving DecidableEq, Repr

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
following different papers (@cite{martin-rose-nichols-2025}, @cite{goldberg-jackendoff-2004}, @cite{embick-2009}).
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
    Causative.cause ≠ resultativeCausativeBuilder := by
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

/-- All resultative entries have BECOME (via derived subevent). -/
theorem all_have_become :
    allEntries.all (·.dualSubevent.constructional.hasBecome) = true := by
  native_decide

/-- Inception presupposes ¬P before. -/
theorem inception_presupposes_not_prior {W : Type*} (P : W → Prop) (w : W) :
    priorStatePresup .inception P w ↔ ¬P w := Iff.rfl

/-- Inception asserts P after. -/
theorem inception_asserts_result {W : Type*} (P : W → Prop) :
    resultStateAssertion .inception P = P := rfl

/-! ## Müller Decomposability

All four resultative subconstructions are fully abstract and therefore
decomposable into Müller's universal schemata.

Causative subconstructions → [HS, HC, HC] (same as parent resultative)
Noncausative subconstructions → [HS, HC] (intransitive, fewer complements) -/

/-- All four subconstructions are fully compositional. -/
theorem allResultativesFullyCompositional :
    resultativeFamily.all (λ c =>
      isFullyCompositional c.construction) = true := by
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

/-! ## Cross-linguistic Resultative Parameters (@cite{tay-2024})

Resultative constructions vary cross-linguistically along dimensions orthogonal
to the G&J subconstruction typology. @cite{tay-2024} identifies three:
realization (how the result predicate is morphosyntactically encoded),
orientation (whether DOR holds), and phase grammaticalization. -/

section CrossLinguistic

/-- How the result predicate is morphosyntactically realized. -/
inductive ResultativeRealization where
  /-- English: result AP/PP is a syntactic adjunct -/
  | syntacticAdjunct
  /-- Mandarin V-V: V2 morphologically incorporated into V1 -/
  | verbCompound
  /-- Mandarin V-de: result clause introduced by particle de -/
  | deComplement
  deriving DecidableEq, Repr

/-- Whether the result predicate targets the subject or object.
    English enforces DOR (Direct Object Restriction): the result must
    predicate of the direct object. Mandarin allows subject-oriented
    resultatives productively (kū-lèi "cry-tired"). -/
inductive ResultOrientation where
  | objectOriented
  | subjectOriented
  deriving DecidableEq, Repr

/-- Phase complements: a grammaticalized closed-class subset of Mandarin
    V2 resultatives with fixed change-of-state semantics.
    Maps to `CoSType` from `ChangeOfState.Theory`. -/
inductive PhaseComplement where
  | dao   -- 倒 dǎo "fall" → inception of horizontal/fallen state
  | wan   -- 完 wán "finish" → cessation of activity
  | hao   -- 好 hǎo "good" → inception of satisfactory/completed state
  | diao  -- 掉 diào "fall off" → inception of detachment/disappearance
  | zhu   -- 住 zhù "hold" → continuation of state
  deriving DecidableEq, Repr

/-- Phase complements have fixed CoS semantics, bridging Mandarin morphology
    to the cross-linguistic `CoSType` infrastructure in `ChangeOfState.Theory`. -/
def PhaseComplement.cosType : PhaseComplement → CoSType
  | .dao  => .inception
  | .wan  => .cessation
  | .hao  => .inception
  | .diao => .inception
  | .zhu  => .continuation

/-- All inceptive phase complements share the presupposition ¬P. -/
theorem inceptive_phases_share_presup :
    PhaseComplement.dao.cosType = .inception ∧
    PhaseComplement.hao.cosType = .inception ∧
    PhaseComplement.diao.cosType = .inception := ⟨rfl, rfl, rfl⟩

/-- Phase complements cover all three CoS types (inception, cessation, continuation). -/
theorem phase_complements_cover_cos_types :
    PhaseComplement.dao.cosType = .inception ∧
    PhaseComplement.wan.cosType = .cessation ∧
    PhaseComplement.zhu.cosType = .continuation := ⟨rfl, rfl, rfl⟩

end CrossLinguistic

/-! ### V2 namespace for new code

Legacy resultative models above are built on `CausalDynamics` + `Situation`.
V2 mirrors them on `BoolSEM` + `Valuation` substrate. Each scenario
gets its own enum (`Fintype + DecidableEq + Repr`) so kernel reduction
closes the structural sufficiency/completion theorems without
`native_decide`. Pattern matches `Lewis1973.lean`: local `developDetOn`-
based predicates (no `IsDAG` required for these structural proofs;
`Sufficiency.V2.makeSem` / `CCSelection.V2.completesForEffect` are
available for downstream V2 consumers via the hub V2 surfaces).

The big `independent_source_disrupts_tightness` proof (legacy
`applyLawsOnce`/`isFixpoint` reasoning over `CausalDynamics`) is not
ported here — the qualitative claim is witnessed concretely by
`KickDoorViaBall.kick_door_via_ball_not_tight`. -/

namespace V2

open Core.Causal.V2 Core.Causal.V2.Mechanism Core.Causal.V2.SEM

/-- Local sufficiency predicate (V2): with `cause` set true under
    `bg`, `developDetOn` of `M` produces `effect = true`. -/
noncomputable def sufficient {W : Type*} [Fintype W] [DecidableEq W]
    (M : BoolSEM W) [SEM.IsDeterministic M]
    (vs : List W) (bg : Valuation (fun _ : W => Bool)) (n : Nat)
    (cause effect : W) : Prop :=
  (developDetOn M vs n (bg.extend cause true)).hasValue effect true

/-- Local completion predicate (V2): sufficient + but-for. -/
noncomputable def completes {W : Type*} [Fintype W] [DecidableEq W]
    (M : BoolSEM W) [SEM.IsDeterministic M]
    (vs : List W) (bg : Valuation (fun _ : W => Bool)) (n : Nat)
    (cause effect : W) : Prop :=
  sufficient M vs bg n cause effect ∧
  ¬ (developDetOn M vs n (bg.extend cause false)).hasValue effect true

-- ════════════════════════════════════════════════════
-- § HammerFlat: hammering → flat
-- ════════════════════════════════════════════════════

namespace HammerFlat

inductive V | hammering | flat
  deriving DecidableEq, Fintype, Repr

def varList : List V := [.hammering, .flat]

def graph : CausalGraph V := ⟨fun | .hammering => ∅ | .flat => {.hammering}⟩

noncomputable def model : BoolSEM V :=
  { graph := graph
    mech := fun
      | .hammering => const (G := graph) false
      | .flat => deterministic (fun ρ => ρ ⟨.hammering, by simp [graph]⟩) }

noncomputable instance : SEM.IsDeterministic model where
  mech_det v := match v with
    | .hammering => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .flat => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

theorem hammer_sufficient_for_flat :
    sufficient model varList Valuation.empty 1 .hammering .flat := by
  unfold sufficient; rfl

theorem hammer_completes_flat :
    completes model varList Valuation.empty 1 .hammering .flat := by
  refine ⟨by unfold sufficient; rfl, ?_⟩
  intro h; exact Bool.false_ne_true (Option.some.inj h)

end HammerFlat

-- ════════════════════════════════════════════════════
-- § KickIntoField: kicking → in_field
-- ════════════════════════════════════════════════════

namespace KickIntoField

inductive V | kicking | in_field
  deriving DecidableEq, Fintype, Repr

def varList : List V := [.kicking, .in_field]

def graph : CausalGraph V := ⟨fun | .kicking => ∅ | .in_field => {.kicking}⟩

noncomputable def model : BoolSEM V :=
  { graph := graph
    mech := fun
      | .kicking => const (G := graph) false
      | .in_field => deterministic (fun ρ => ρ ⟨.kicking, by simp [graph]⟩) }

noncomputable instance : SEM.IsDeterministic model where
  mech_det v := match v with
    | .kicking => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .in_field => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

theorem kick_sufficient_for_field :
    sufficient model varList Valuation.empty 1 .kicking .in_field := by
  unfold sufficient; rfl

theorem kick_completes_field :
    completes model varList Valuation.empty 1 .kicking .in_field := by
  refine ⟨by unfold sufficient; rfl, ?_⟩
  intro h; exact Bool.false_ne_true (Option.some.inj h)

end KickIntoField

-- ════════════════════════════════════════════════════
-- § LaughSilly: laughing → silly (fake reflexive)
-- ════════════════════════════════════════════════════

namespace LaughSilly

inductive V | laughing | silly
  deriving DecidableEq, Fintype, Repr

def varList : List V := [.laughing, .silly]

def graph : CausalGraph V := ⟨fun | .laughing => ∅ | .silly => {.laughing}⟩

noncomputable def model : BoolSEM V :=
  { graph := graph
    mech := fun
      | .laughing => const (G := graph) false
      | .silly => deterministic (fun ρ => ρ ⟨.laughing, by simp [graph]⟩) }

noncomputable instance : SEM.IsDeterministic model where
  mech_det v := match v with
    | .laughing => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .silly => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

theorem laugh_sufficient_for_silly :
    sufficient model varList Valuation.empty 1 .laughing .silly := by
  unfold sufficient; rfl

end LaughSilly

-- ════════════════════════════════════════════════════
-- § FreezeSolid: noncausative (no edges)
-- ════════════════════════════════════════════════════

namespace FreezeSolid

inductive V | freezing | solid
  deriving DecidableEq, Fintype, Repr

def varList : List V := [.freezing, .solid]

/-- Empty graph: no causal relations (noncausative resultative). -/
def graph : CausalGraph V := ⟨fun _ => ∅⟩

noncomputable def model : BoolSEM V :=
  { graph := graph
    mech := fun _ => const (G := graph) false }

noncomputable instance : SEM.IsDeterministic model where
  mech_det _ := inferInstanceAs (Mechanism.IsDeterministic (const _))

/-- Freezing is NOT sufficient for solidity in the empty-edge model. -/
theorem freeze_not_sufficient :
    ¬ sufficient model varList Valuation.empty 1 .freezing .solid := by
  intro h
  unfold sufficient at h
  exact Bool.false_ne_true (Option.some.inj h)

end FreezeSolid

-- ════════════════════════════════════════════════════
-- § DrinkTeapotDry: drinking → tea_removal → teapot_dry (passive chain)
-- ════════════════════════════════════════════════════

namespace DrinkTeapotDry

inductive V | drinking | tea_removal | teapot_dry
  deriving DecidableEq, Fintype, Repr

def varList : List V := [.drinking, .tea_removal, .teapot_dry]

def graph : CausalGraph V := ⟨fun
  | .drinking => ∅
  | .tea_removal => {.drinking}
  | .teapot_dry => {.tea_removal}⟩

noncomputable def model : BoolSEM V :=
  { graph := graph
    mech := fun
      | .drinking => const (G := graph) false
      | .tea_removal => deterministic (fun ρ => ρ ⟨.drinking, by simp [graph]⟩)
      | .teapot_dry => deterministic (fun ρ => ρ ⟨.tea_removal, by simp [graph]⟩) }

noncomputable instance : SEM.IsDeterministic model where
  mech_det v := match v with
    | .drinking => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .tea_removal => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))
    | .teapot_dry => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

/-- Tight despite being a chain: removing drinking leaves tea_removal
    undetermined (no independent source), so teapot_dry doesn't fire. -/
theorem drink_completes_dry :
    completes model varList Valuation.empty 1 .drinking .teapot_dry := by
  refine ⟨by unfold sufficient; rfl, ?_⟩
  intro h; exact Bool.false_ne_true (Option.some.inj h)

end DrinkTeapotDry

-- ════════════════════════════════════════════════════
-- § KickDoorDirect: kicking → door_open
-- ════════════════════════════════════════════════════

namespace KickDoorDirect

inductive V | kicking | door_open
  deriving DecidableEq, Fintype, Repr

def varList : List V := [.kicking, .door_open]

def graph : CausalGraph V := ⟨fun | .kicking => ∅ | .door_open => {.kicking}⟩

noncomputable def model : BoolSEM V :=
  { graph := graph
    mech := fun
      | .kicking => const (G := graph) false
      | .door_open => deterministic (fun ρ => ρ ⟨.kicking, by simp [graph]⟩) }

noncomputable instance : SEM.IsDeterministic model where
  mech_det v := match v with
    | .kicking => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .door_open => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

theorem kick_door_completes_direct :
    completes model varList Valuation.empty 1 .kicking .door_open := by
  refine ⟨by unfold sufficient; rfl, ?_⟩
  intro h; exact Bool.false_ne_true (Option.some.inj h)

end KickDoorDirect

-- ════════════════════════════════════════════════════
-- § KickDoorViaBall: kicking → ball_motion → door_open + ball_energy → ball_motion
-- ════════════════════════════════════════════════════

namespace KickDoorViaBall

inductive V | kicking | ball_motion | ball_energy | door_open
  deriving DecidableEq, Fintype, Repr

def varList : List V := [.kicking, .ball_energy, .ball_motion, .door_open]

/-- Ball motion has TWO parents: kicking and ball_energy. The ball
    has its own independent energy source, so kicking is not necessary. -/
def graph : CausalGraph V := ⟨fun
  | .kicking => ∅
  | .ball_energy => ∅
  | .ball_motion => {.kicking, .ball_energy}
  | .door_open => {.ball_motion}⟩

/-- Ball motion fires if EITHER kicking or ball_energy is true (∨-mechanism). -/
noncomputable def model : BoolSEM V :=
  { graph := graph
    mech := fun
      | .kicking => const (G := graph) false
      | .ball_energy => const (G := graph) false
      | .ball_motion => deterministic (fun ρ =>
          ρ ⟨.kicking, by simp [graph]⟩ || ρ ⟨.ball_energy, by simp [graph]⟩)
      | .door_open => deterministic (fun ρ => ρ ⟨.ball_motion, by simp [graph]⟩) }

noncomputable instance : SEM.IsDeterministic model where
  mech_det v := match v with
    | .kicking => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .ball_energy => inferInstanceAs (Mechanism.IsDeterministic (const _))
    | .ball_motion => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))
    | .door_open => inferInstanceAs (Mechanism.IsDeterministic (deterministic _))

/-- Background where the ball has its own energy. -/
def ballHasEnergyBg : Valuation (fun _ : V => Bool) :=
  Valuation.empty.extend .ball_energy true

/-- NOT tight: removing kicking still allows ball_energy → ball_motion
    → door_open. The kick is not necessary. -/
theorem kick_door_via_ball_not_tight :
    ¬ completes model varList ballHasEnergyBg 1 .kicking .door_open := by
  intro ⟨_, hNot⟩
  apply hNot
  rfl

end KickDoorViaBall

end V2

end Semantics.Causation.Resultatives
