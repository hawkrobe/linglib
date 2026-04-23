import Linglib.Core.Lexical.VerbClass
import Linglib.Core.Causal.SEM.Counterfactual
import Linglib.Core.Causal.SEM.Monotonicity
import Linglib.Core.Causal.V2.SEM.Counterfactual
import Linglib.Theories.Semantics.Causation.Sufficiency
import Linglib.Theories.Semantics.Attitudes.Intensional
import Linglib.Theories.Semantics.Tense.Aspect.Core

/-!
# Implicative Verb Semantics
@cite{nadathur-2024} @cite{karttunen-1971} @cite{nadathur-lauer-2020}

Causal Semantics for Implicative Verbs. Journal of Semantics 40: 311–358.

## Core Insight: The Prerequisite Account (Proposal 32)

Implicative verbs (*manage*, *dare*, *fail*) have complement entailments
derived from causal structure. The **prerequisite account** (Proposal 32)
decomposes implicative meaning into three components:

- **(32i) Presuppose**: ∃ prerequisite A(x) causally necessary for P(x)
- **(32ii) Assert**: x did A — the subject satisfied the prerequisite
- **(32iii) Presuppose** (two-way only): A(x) is the only unresolved
  causally necessary condition, hence causally sufficient for P(x)

One-way implicatives (*jaksaa* 'have the strength', *pystyä* 'be able')
have only (32i)–(32ii), not (32iii). The missing positive entailment
arises as a defeasible **antiperfection implicature** via circumscription.

## Causal Grounding

`manageSem` (causal sufficiency of the prerequisite for the complement)
is **derived** from the prerequisite account: when both the necessity
presupposition (32i) and sufficiency presupposition (32iii) hold, and
the assertion (32ii) establishes that A(x) is true, complement truth
follows as a causal consequence. The entailment is not stipulated but
emerges from the causal model.

## Lexically-Specified Prerequisites

Specific implicatives lexicalize **which** prerequisite matters:
- *dare/uskaltaa* → courage
- *bother/viitsiä* → engagement/effort
- *malttaa* → patience
- *hennoa* → hard-heartedness
- *jaksaa* → strength
- *manage/onnistua* → underspecified (contextual enrichment)

-/

namespace Semantics.Causation.Implicative

open Core (WorldTimeIndex)

open Core.Causal
open Core.Verbs (Implicative)

-- ════════════════════════════════════════════════════
-- § Prerequisite Types (@cite{nadathur-2024})
-- ════════════════════════════════════════════════════

/-- Lexically-specified prerequisite types for implicative verbs.

    The chief dimension of semantic variation between implicative verbs
    lies in what they lexicalize about the nature of the prerequisite —
    the sort of activity needed to overcome the potential obstacle.

    Specific verbs (*dare*, *bother*) name their prerequisites; bleached
    verbs (*manage*, *onnistua*) leave the prerequisite underspecified. -/
inductive Prerequisite where
  | courage          -- dare, uskaltaa: daring/courageous action
  | engagement       -- bother, viitsiä: overcoming apathy, making the effort
  | patience         -- malttaa: exercising patience
  | hardHeartedness  -- hennoa: having the heart (hard-heartedness)
  | strength         -- jaksaa: having the required strength
  | fitness          -- mahtua: fitting (being small enough)
  | time             -- ehtiä: finding/making time
  | shamelessness    -- kehdata: acting without shame
  | unspecified      -- manage, onnistua: contextually enriched
  deriving DecidableEq, Repr

/-- Is the prerequisite lexically specific (names a particular condition)
    or underspecified (contextual enrichment)? -/
def Prerequisite.isSpecific : Prerequisite → Bool
  | .unspecified => false
  | _ => true

-- ════════════════════════════════════════════════════
-- § ImplicativeScenario and Semantics
-- ════════════════════════════════════════════════════

/-- A scenario for implicative verbs: a causal model linking a prerequisite
    action to a complement outcome.

    The `prerequisite` variable represents A(x) — the causally-relevant
    condition whose satisfaction (or non-satisfaction) determines the
    complement outcome via the causal dynamics. For *dare*, A(x) =
    "x was daring/courageous"; for *manage*, A(x) is underspecified. -/
structure ImplicativeScenario where
  /-- The causal dynamics (structural equations) -/
  dynamics : CausalDynamics
  /-- The prerequisite variable A(x) — the condition whose satisfaction
      is asserted by the implicative verb (@cite{nadathur-2024} Proposal 32ii) -/
  prerequisite : Variable
  /-- The complement variable P(x) — the VP outcome -/
  complement : Variable
  /-- The background situation c -/
  background : Situation

/-- Semantics of "manage": the prerequisite was causally sufficient for the
    complement outcome.

    This is the **derived prediction** of Proposal 32 for two-way implicatives:
    when A(x) is presupposed to be both causally necessary (32i) and causally
    sufficient (32iii) for P(x), and A(x) holds (32ii), then P(x) follows
    as a causal consequence of A(x) + the background situation.

    The old label "action" has been renamed to "prerequisite" to match
    @cite{nadathur-2024}'s terminology. -/
def manageSem (sc : ImplicativeScenario) : Prop :=
  (normalDevelopment sc.dynamics (sc.background.extend sc.prerequisite true)).hasValue
    sc.complement true

instance (sc : ImplicativeScenario) : Decidable (manageSem sc) :=
  inferInstanceAs (Decidable (Situation.hasValue ..))

/-- Bridge: `manageSem ↔ causallySufficient` over the scenario fields. -/
theorem manageSem_iff_causallySufficient (sc : ImplicativeScenario) :
    manageSem sc ↔
      causallySufficient sc.dynamics sc.background sc.prerequisite sc.complement :=
  Iff.rfl

/-- Semantics of "fail": the complement did NOT develop.

    "Kim failed to swim across" entails "Kim did not swim across."
    Dual of `manageSem`: `failSem sc ↔ ¬ manageSem sc`. -/
def failSem (sc : ImplicativeScenario) : Prop :=
  ¬ manageSem sc

instance (sc : ImplicativeScenario) : Decidable (failSem sc) :=
  inferInstanceAs (Decidable (¬ _))

/-- **Central grounding theorem**: if `manageSem` holds, the complement
    is true after normal development. -/
theorem manage_entails_complement (sc : ImplicativeScenario)
    (h : manageSem sc) :
    (normalDevelopment sc.dynamics (sc.background.extend sc.prerequisite true)).hasValue
      sc.complement true := h

/-- If `failSem` holds, the complement is not true after normal development. -/
theorem fail_entails_not_complement (sc : ImplicativeScenario)
    (h : failSem sc) :
    ¬ (normalDevelopment sc.dynamics (sc.background.extend sc.prerequisite true)).hasValue
      sc.complement true := h

/-- Implicative entailment is NOT aspect-governed: the entailment holds with
    no aspect parameter. -/
theorem implicative_not_aspect_governed (sc : ImplicativeScenario)
    (h : manageSem sc) :
    (normalDevelopment sc.dynamics (sc.background.extend sc.prerequisite true)).hasValue
      sc.complement true :=
  manage_entails_complement sc h

-- ════════════════════════════════════════════════════
-- § Prerequisite Account (@cite{nadathur-2024} Proposal 32)
-- ════════════════════════════════════════════════════

/-- **Proposal 32**: The prerequisite account of implicative semantics.

    For a two-way implicative I, agent x, predicate P, background c:
    - (32i)   Presupposes: ∃ prerequisite A(x) causally necessary for P(x)
    - (32ii)  Asserts: x did A (A(x) holds)
    - (32iii) Presupposes: A(x) is causally sufficient for P(x) in c

    One-way verbs have only (32i) and (32ii); (32iii) is absent, so the
    positive entailment is merely an antiperfection implicature.

    The `prerequisiteType` field identifies which lexical prerequisite
    the verb encodes; `hasSufficiencyPresup` distinguishes one-way from
    two-way verbs. -/
structure PrerequisiteAccount where
  /-- The causal dynamics governing the scenario -/
  dynamics : CausalDynamics
  /-- Background situation c -/
  background : Situation
  /-- The prerequisite variable A(x) -/
  prereqVar : Variable
  /-- The complement variable P(x) -/
  complementVar : Variable
  /-- What kind of prerequisite A is (courage, patience, etc.) -/
  prerequisiteType : Prerequisite
  /-- (32iii): Does this verb presuppose causal sufficiency?
      `true` for two-way implicatives (manage, dare);
      `false` for one-way implicatives (jaksaa, pystyä). -/
  hasSufficiencyPresup : Bool

/-- (32i): The necessity presupposition holds — A(x) is causally necessary
    for P(x) relative to the background. -/
def PrerequisiteAccount.necessityPresup (pa : PrerequisiteAccount) : Prop :=
  causallyNecessary pa.dynamics pa.background pa.prereqVar pa.complementVar

instance (pa : PrerequisiteAccount) : Decidable pa.necessityPresup :=
  inferInstanceAs (Decidable (causallyNecessary ..))

/-- (32iii): **Check** whether A(x) is causally sufficient for P(x) in
    the model. This is a computed property of the dynamics/background,
    distinct from `hasSufficiencyPresup` (a lexical property of the verb).
    For well-formed accounts, `sufficiencyPresup ↔ hasSufficiencyPresup`. -/
def PrerequisiteAccount.sufficiencyPresup (pa : PrerequisiteAccount) : Prop :=
  (normalDevelopment pa.dynamics (pa.background.extend pa.prereqVar true)).hasValue
    pa.complementVar true

instance (pa : PrerequisiteAccount) : Decidable pa.sufficiencyPresup :=
  inferInstanceAs (Decidable (Situation.hasValue ..))

/-- (32ii): The assertion — A(x) holds in the evaluation world. -/
def PrerequisiteAccount.assertion (pa : PrerequisiteAccount) (w : Situation) : Prop :=
  w.hasValue pa.prereqVar true

instance (pa : PrerequisiteAccount) (w : Situation) : Decidable (pa.assertion w) :=
  inferInstanceAs (Decidable (Situation.hasValue ..))

/-- Convert a prerequisite account to the `ImplicativeScenario` used by
    `manageSem`/`failSem`. Shows that the scenario-level semantics is
    derived from the prerequisite account, not primitive. -/
def PrerequisiteAccount.toScenario (pa : PrerequisiteAccount) : ImplicativeScenario :=
  { dynamics := pa.dynamics
    prerequisite := pa.prereqVar
    complement := pa.complementVar
    background := pa.background }

/-- For two-way implicatives: if the necessity presupposition (32i),
    sufficiency presupposition (32iii), and assertion (32ii) all hold,
    then `manageSem` holds — complement truth follows.

    This derives the complement entailment from the prerequisite
    account rather than stipulating it. -/
theorem prerequisite_derives_manageSem (pa : PrerequisiteAccount)
    (hSuf : pa.sufficiencyPresup) :
    manageSem pa.toScenario := hSuf

-- ════════════════════════════════════════════════════
-- § Directionality
-- ════════════════════════════════════════════════════

/-- Directionality of complement entailment (@cite{nadathur-2024}).

    - **oneWay**: complement entailment under only one matrix polarity.
      For polarity-preserving verbs (*jaksaa*), negation entails ¬VP
      but affirmation only *implicates* VP (via antiperfection).
      For polarity-reversing verbs (*hesitate*), negation entails VP
      but affirmation doesn't entail ¬VP.
    - **twoWay**: complement entailment under both polarities
      ("manage to VP" → VP; "not manage to VP" → ¬VP).

    @cite{nadathur-2024} derives this from causal structure: two-way = both
    necessity and sufficiency presupposed (32i + 32iii); one-way = only
    necessity presupposed (32i). -/
inductive Directionality where
  | oneWay    -- only necessity presupposed; positive entailment is an implicature
  | twoWay    -- necessity + sufficiency presupposed (manage, dare, fail)
  deriving DecidableEq, Repr

/-- The directionality of a prerequisite account is determined by whether
    causal sufficiency is presupposed (32iii). Two-way verbs presuppose
    sufficiency; one-way verbs do not. -/
def PrerequisiteAccount.directionality (pa : PrerequisiteAccount) : Directionality :=
  if pa.hasSufficiencyPresup then .twoWay else .oneWay

-- ════════════════════════════════════════════════════
-- § Concrete Example: "manage to swim across"
-- ════════════════════════════════════════════════════

section ConcreteExample

/-- The prerequisite: trying/effort to swim across -/
private def tryAction : Variable := mkVar "trySwim"

/-- The complement: swimming across successfully -/
private def swimAcross : Variable := mkVar "swimAcross"

/-- Causal dynamics: the prerequisite (trying) is sufficient for swimming across
    (in the scenario where "manage" is appropriate). -/
private def manageDyn : CausalDynamics :=
  CausalDynamics.ofList [CausalLaw.simple tryAction swimAcross]

/-- The concrete scenario for "Kim managed to swim across". -/
private def manageScenario : ImplicativeScenario where
  dynamics := manageDyn
  prerequisite := tryAction
  complement := swimAcross
  background := Situation.empty

/-- Concrete verification: manageSem holds for the swim scenario. -/
theorem manage_swim_holds : manageSem manageScenario := by native_decide

/-- Concrete verification: the complement (swimming across) is true. -/
theorem manage_swim_complement_true :
    (normalDevelopment manageScenario.dynamics
      (manageScenario.background.extend manageScenario.prerequisite true)).hasValue
      manageScenario.complement true := by native_decide

/-- The fail scenario: same dynamics, but testing failSem.
    If the dynamics DO fire (prerequisite sufficient for complement), failSem is false. -/
theorem fail_swim_false_when_sufficient :
    ¬ failSem manageScenario := by native_decide

/-- A scenario where the prerequisite is NOT sufficient (no causal law). -/
private def failScenario : ImplicativeScenario where
  dynamics := CausalDynamics.empty  -- no law connecting prerequisite to complement
  prerequisite := tryAction
  complement := swimAcross
  background := Situation.empty

/-- When there's no causal connection, failSem holds (complement doesn't develop). -/
theorem fail_no_law_holds : failSem failScenario := by native_decide

end ConcreteExample

-- ════════════════════════════════════════════════════
-- § Implicative.toSemantics: map polarity to causal semantics
-- ════════════════════════════════════════════════════

end Semantics.Causation.Implicative

namespace Core.Verbs

/-- Map to the compositional semantics (`manageSem` or `failSem`). -/
def Implicative.toSemantics : Implicative →
    (Semantics.Causation.Implicative.ImplicativeScenario → Prop)
  | .positive => Semantics.Causation.Implicative.manageSem
  | .negative => Semantics.Causation.Implicative.failSem

end Core.Verbs

namespace Semantics.Causation.Implicative

open Core.Causal
open Core.Verbs (Implicative)

/-- Positive builder entails complement: if `manageSem` holds, complement is true. -/
theorem positive_entails_complement (sc : ImplicativeScenario)
    (h : Implicative.positive.toSemantics sc) :
    (normalDevelopment sc.dynamics (sc.background.extend sc.prerequisite true)).hasValue
      sc.complement true :=
  manage_entails_complement sc h

/-- Negative builder entails NOT complement: if `failSem` holds, complement is false. -/
theorem negative_entails_not_complement (sc : ImplicativeScenario)
    (h : Implicative.negative.toSemantics sc) :
    ¬ (normalDevelopment sc.dynamics (sc.background.extend sc.prerequisite true)).hasValue
      sc.complement true :=
  fail_entails_not_complement sc h

/-- `entailsComplement` matches semantic behavior: positive ↔ `manageSem`,
    negative ↔ `failSem`. -/
theorem entailsComplement_positive :
    Implicative.positive.entailsComplement = true := rfl

theorem entailsComplement_negative :
    Implicative.negative.entailsComplement = false := rfl

-- ════════════════════════════════════════════════════
-- § ImplicativeClass: Full Classification
-- ════════════════════════════════════════════════════

/-- Full classification of complement-entailing verbs.

    The four parameters:
    - **polarity**: positive (manage → complement true) vs
      negative (fail → complement false)
    - **directionality**: one-way vs two-way complement entailment
    - **aspectGoverned**: whether aspect modulates the entailment (true for
      ability modals & enough/too; false for lexical implicatives)
    - **prerequisite**: what kind of causal prerequisite the verb lexicalizes
      (@cite{nadathur-2024}) -/
structure ImplicativeClass where
  /-- Positive (manage, force) or negative (fail, prevent) polarity -/
  polarity : Implicative
  /-- One-way (ability) or two-way (manage) entailment -/
  directionality : Directionality
  /-- Does aspect govern the actuality inference? -/
  aspectGoverned : Bool
  /-- Lexically-specified prerequisite type (if any) -/
  prerequisite : Option Prerequisite := none
  deriving DecidableEq, Repr

-- Instances for standard verb classes

/-- *manage*: two-way positive, not aspect-governed, unspecified prerequisite.
    "managed to VP" → VP; "didn't manage to VP" → ¬VP. -/
def ImplicativeClass.manage : ImplicativeClass :=
  { polarity := .positive, directionality := .twoWay, aspectGoverned := false
    prerequisite := some .unspecified }

/-- *fail*: two-way negative, not aspect-governed, unspecified prerequisite. -/
def ImplicativeClass.fail : ImplicativeClass :=
  { polarity := .negative, directionality := .twoWay, aspectGoverned := false
    prerequisite := some .unspecified }

/-- *dare/uskaltaa*: two-way positive, prerequisite = courage. -/
def ImplicativeClass.dare : ImplicativeClass :=
  { polarity := .positive, directionality := .twoWay, aspectGoverned := false
    prerequisite := some .courage }

/-- *bother/viitsiä*: two-way positive, prerequisite = engagement. -/
def ImplicativeClass.bother : ImplicativeClass :=
  { polarity := .positive, directionality := .twoWay, aspectGoverned := false
    prerequisite := some .engagement }

/-- *jaksaa* 'have the strength': one-way positive, prerequisite = strength.
    Positive assertion ↛ complement; only negative entails. -/
def ImplicativeClass.jaksaa : ImplicativeClass :=
  { polarity := .positive, directionality := .oneWay, aspectGoverned := false
    prerequisite := some .strength }

/-- *be able*: one-way positive, aspect-governed. -/
def ImplicativeClass.ability : ImplicativeClass :=
  { polarity := .positive, directionality := .oneWay, aspectGoverned := true }

/-- *enough to VP*: one-way positive, aspect-governed. -/
def ImplicativeClass.enough : ImplicativeClass :=
  { polarity := .positive, directionality := .oneWay, aspectGoverned := true }

/-- *too Adj to VP*: one-way negative, aspect-governed. -/
def ImplicativeClass.too : ImplicativeClass :=
  { polarity := .negative, directionality := .oneWay, aspectGoverned := true }

/-- *hesitate/epäröidä*: polarity-reversing one-way.
    "hesitated to VP" ↛ ¬VP; "didn't hesitate to VP" → VP.
    (@cite{nadathur-2024}) -/
def ImplicativeClass.hesitate : ImplicativeClass :=
  { polarity := .negative, directionality := .oneWay, aspectGoverned := false
    prerequisite := some .courage }

-- Classification theorems

/-- Manage and fail differ only in polarity. -/
theorem manage_fail_polarity :
    ImplicativeClass.manage.directionality = ImplicativeClass.fail.directionality ∧
    ImplicativeClass.manage.aspectGoverned = ImplicativeClass.fail.aspectGoverned ∧
    ImplicativeClass.manage.polarity ≠ ImplicativeClass.fail.polarity := by
  exact ⟨rfl, rfl, by decide⟩

/-- Ability and manage differ: ability is aspect-governed and one-way. -/
theorem ability_vs_manage :
    ImplicativeClass.ability.aspectGoverned = true ∧
    ImplicativeClass.manage.aspectGoverned = false ∧
    ImplicativeClass.ability.directionality = .oneWay ∧
    ImplicativeClass.manage.directionality = .twoWay := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Enough and too share aspect-governance but differ in polarity. -/
theorem enough_too_polarity :
    ImplicativeClass.enough.aspectGoverned = ImplicativeClass.too.aspectGoverned ∧
    ImplicativeClass.enough.directionality = ImplicativeClass.too.directionality ∧
    ImplicativeClass.enough.polarity ≠ ImplicativeClass.too.polarity := by
  exact ⟨rfl, rfl, by decide⟩

/-- Dare and manage share polarity and directionality but differ in prerequisite. -/
theorem dare_vs_manage_prerequisite :
    ImplicativeClass.dare.polarity = ImplicativeClass.manage.polarity ∧
    ImplicativeClass.dare.directionality = ImplicativeClass.manage.directionality ∧
    ImplicativeClass.dare.prerequisite ≠ ImplicativeClass.manage.prerequisite := by
  exact ⟨rfl, rfl, by decide⟩

/-- Jaksaa (one-way) vs uskaltaa/dare (two-way): same prerequisite specificity,
    different directionality — derived from whether sufficiency is presupposed. -/
theorem jaksaa_vs_dare_directionality :
    ImplicativeClass.jaksaa.directionality = .oneWay ∧
    ImplicativeClass.dare.directionality = .twoWay ∧
    ImplicativeClass.jaksaa.prerequisite.isSome = true ∧
    ImplicativeClass.dare.prerequisite.isSome = true := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- Specific implicatives have specific prerequisites; bleached ones don't. -/
theorem specific_vs_bleached :
    (ImplicativeClass.dare.prerequisite.bind (some ·.isSpecific)) = some true ∧
    (ImplicativeClass.manage.prerequisite.bind (some ·.isSpecific)) = some false := by
  exact ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § PrerequisiteAccount → ImplicativeClass Bridge
-- ════════════════════════════════════════════════════

/-- Derive the full `ImplicativeClass` from a `PrerequisiteAccount`.

    Polarity (positive/negative) must be supplied externally — it is a
    lexical choice orthogonal to causal structure. The prerequisite
    account determines directionality and prerequisite type; lexical
    implicatives are never aspect-governed. -/
def PrerequisiteAccount.toImplicativeClass (pa : PrerequisiteAccount)
    (polarity : Implicative) : ImplicativeClass :=
  { polarity := polarity
    directionality := pa.directionality
    aspectGoverned := false
    prerequisite := some pa.prerequisiteType }

end Semantics.Causation.Implicative

-- ════════════════════════════════════════════════════════════════
-- Causal Frame: Unified Abstraction for Complement-Entailing Constructions
-- (formerly ComplementEntailing.lean)
-- ════════════════════════════════════════════════════════════════

/-!
## Causal Frame
@cite{nadathur-2023} @cite{nadathur-lauer-2020}

The single parameterized type underlying implicative verbs (*manage*, *fail*),
ability modals (*be able*, *sak*), light verbs (*le*), and degree constructions
(*enough/too*).

All complement-entailing constructions share the same causal skeleton:
1. A **causal dynamics** (structural equations)
2. A **trigger variable** (action, degree threshold, managing event)
3. A **complement variable** (the VP outcome)
4. A **background function** mapping evaluation contexts to causal situations
5. An **actualization mode** controlling what asserts trigger occurrence

| Instance | Trigger | Actualization |
|----------|---------|---------------|
| *manage* | managing event | `.lexical` (aspect-independent) |
| *le* (Hindi LV) | volitional choice | `.lexical` (aspect-independent) |
| *be able* / *sak* | agent's action | `.aspectual` (PFV/IMPF) |
| *enough to VP* | degree ≥ θ | `.aspectual` (PFV/IMPF) |
-/

namespace Semantics.Causation.ComplementEntailing

open Core.Causal
open Semantics.Tense.Aspect.Core (ViewpointAspectB)

-- ════════════════════════════════════════════════════
-- § ActualizationMode
-- ════════════════════════════════════════════════════

/-- How the actuality of the trigger gets asserted.

    - **lexical**: The verb's lexical semantics asserts that the trigger occurred.
      The complement entailment holds regardless of grammatical aspect.
      (*manage*, *fail*, *force*, *prevent*, *le*)

    - **aspectual**: Grammatical aspect determines whether the trigger's
      occurrence is asserted. Perfective asserts it; imperfective doesn't.
      (*be able*, *sak*, *enough to VP*, *too Adj to VP*) -/
inductive ActualizationMode where
  | lexical    -- trigger asserted by lexical semantics (aspect-independent)
  | aspectual  -- trigger asserted by perfective aspect only
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § CausalFrame
-- ════════════════════════════════════════════════════

/-- **CausalFrame**: The abstract frame underlying all complement-entailing
    verb constructions.

    Parameterized by `W` (evaluation context type):
    - `W = Unit` for implicative verbs (no modal dimension)
    - `W = World` for ability modals (Kripke worlds)
    - `W = World` for degree constructions (degree evaluated at worlds)

    The frame bundles:
    - Causal model (dynamics + trigger + complement)
    - Background projection (evaluation context → causal situation)
    - Actualization mode (what controls trigger assertion) -/
structure CausalFrame (W : Type*) where
  /-- Structural equations governing trigger → complement -/
  dynamics : CausalDynamics
  /-- The trigger variable (action, degree threshold, managing event) -/
  trigger : Variable
  /-- The complement variable (VP outcome) -/
  complement : Variable
  /-- Maps evaluation contexts to causal background situations -/
  background : W → Situation
  /-- How trigger occurrence is asserted -/
  actualization : ActualizationMode

-- ════════════════════════════════════════════════════
-- § Generic Semantics
-- ════════════════════════════════════════════════════

section FrameSemantics

variable {W : Type*}

/-- Trigger is causally sufficient for complement at evaluation context `w`. -/
def CausalFrame.sufficientAt (f : CausalFrame W) (w : W) : Prop :=
  (normalDevelopment f.dynamics ((f.background w).extend f.trigger true)).hasValue
    f.complement true

instance (f : CausalFrame W) (w : W) : Decidable (f.sufficientAt w) :=
  inferInstanceAs (Decidable (Situation.hasValue ..))

/-- Complement is actualized at `w`: trigger occurred AND complement developed. -/
def CausalFrame.actualizedAt (f : CausalFrame W) (w : W) : Prop :=
  (f.background w).hasValue f.trigger true ∧
  (normalDevelopment f.dynamics (f.background w)).hasValue f.complement true

instance (f : CausalFrame W) (w : W) : Decidable (f.actualizedAt w) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The complement did NOT develop at `w` (for negative-polarity verbs like
    *fail*, *too Adj to VP*). -/
def CausalFrame.complementBlockedAt (f : CausalFrame W) (w : W) : Prop :=
  (f.background w).hasValue f.trigger true ∧
  ¬ (normalDevelopment f.dynamics (f.background w)).hasValue f.complement true

instance (f : CausalFrame W) (w : W) : Decidable (f.complementBlockedAt w) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- **Generic actuality predicate** with aspectual modulation.

    - **Lexical**: sufficiency AND actualization (always, regardless of aspect)
    - **Aspectual + perfective**: sufficiency AND actualization
    - **Aspectual + imperfective**: sufficiency only (no actualization required) -/
def CausalFrame.actualityWithAspect (f : CausalFrame W) (asp : ViewpointAspectB)
    (w : W) : Prop :=
  match f.actualization with
  | .lexical =>
    f.sufficientAt w ∧ f.actualizedAt w
  | .aspectual =>
    match asp with
    | .perfective => f.sufficientAt w ∧ f.actualizedAt w
    | .imperfective => f.sufficientAt w

instance (f : CausalFrame W) (asp : ViewpointAspectB) (w : W) :
    Decidable (f.actualityWithAspect asp w) := by
  unfold CausalFrame.actualityWithAspect
  cases f.actualization
  · exact inferInstanceAs (Decidable (_ ∧ _))
  · cases asp
    · exact inferInstanceAs (Decidable (_ ∧ _))
    · exact inferInstanceAs (Decidable (_ : Prop))

end FrameSemantics

-- ════════════════════════════════════════════════════
-- § Generic Actuality Theorems
-- ════════════════════════════════════════════════════

section ActualityTheorems

variable {W : Type*}

/-- **Generic actuality theorem (lexical mode)**: if a lexically-actualized
    frame holds, the complement is actualized. -/
theorem CausalFrame.lexical_entails_complement (f : CausalFrame W) (w : W)
    (asp : ViewpointAspectB)
    (h : f.actualityWithAspect asp w) (hMode : f.actualization = .lexical) :
    f.actualizedAt w := by
  unfold CausalFrame.actualityWithAspect at h
  rw [hMode] at h
  exact h.2

/-- **Generic actuality theorem (aspectual + perfective)**: if an
    aspect-governed frame holds with perfective aspect, the complement
    is actualized. -/
theorem CausalFrame.perfective_entails_complement (f : CausalFrame W) (w : W)
    (h : f.actualityWithAspect .perfective w)
    (hMode : f.actualization = .aspectual) :
    f.actualizedAt w := by
  unfold CausalFrame.actualityWithAspect at h
  rw [hMode] at h
  exact h.2

/-- **Generic non-entailment (aspectual + imperfective)**: imperfective
    aspect is compatible with complement not being actualized. -/
theorem CausalFrame.imperfective_compatible_with_unrealized :
    ∃ (f : CausalFrame Unit),
      f.actualization = .aspectual ∧
      f.actualityWithAspect .imperfective () ∧
      ¬ f.actualizedAt () := by
  let act := mkVar "act"
  let comp := mkVar "comp"
  let dyn := CausalDynamics.ofList [CausalLaw.simple act comp]
  let f : CausalFrame Unit := {
    dynamics := dyn
    trigger := act
    complement := comp
    background := λ _ => Situation.empty
    actualization := .aspectual
  }
  exact ⟨f, rfl, by native_decide, by native_decide⟩

/-- **Aspect governs actuality (generic)**: the same frame yields different
    entailment patterns under different aspects. -/
theorem CausalFrame.aspect_governs_actuality :
    ∃ (f : CausalFrame Bool),
      f.actualization = .aspectual ∧
      f.actualityWithAspect .perfective true ∧
      f.actualizedAt true ∧
      f.actualityWithAspect .imperfective false ∧
      ¬ f.actualizedAt false := by
  let act := mkVar "act"
  let comp := mkVar "comp"
  let dyn := CausalDynamics.ofList [CausalLaw.simple act comp]
  let f : CausalFrame Bool := {
    dynamics := dyn
    trigger := act
    complement := comp
    background := λ w => if w then Situation.empty.extend act true
                          else Situation.empty
    actualization := .aspectual
  }
  exact ⟨f, rfl, by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- Lexical mode is aspect-independent. -/
theorem CausalFrame.lexical_aspect_independent (f : CausalFrame W) (w : W)
    (hMode : f.actualization = .lexical) :
    f.actualityWithAspect .perfective w ↔ f.actualityWithAspect .imperfective w := by
  unfold CausalFrame.actualityWithAspect
  rw [hMode]

/-- **Imperfective is pure sufficiency** for aspectually-governed frames. -/
theorem CausalFrame.imperfective_is_pure_sufficiency (f : CausalFrame W) (w : W)
    (hMode : f.actualization = .aspectual) :
    f.actualityWithAspect .imperfective w ↔ f.sufficientAt w := by
  unfold CausalFrame.actualityWithAspect
  rw [hMode]

/-- **Perfective adds actualization**: perfective ↔ imperfective ∧ actualized. -/
theorem CausalFrame.perfective_adds_actualization (f : CausalFrame W) (w : W)
    (hMode : f.actualization = .aspectual) :
    f.actualityWithAspect .perfective w ↔
      f.actualityWithAspect .imperfective w ∧ f.actualizedAt w := by
  unfold CausalFrame.actualityWithAspect
  rw [hMode]

end ActualityTheorems

-- ════════════════════════════════════════════════════
-- § Sufficiency relations to causallySufficient
-- ════════════════════════════════════════════════════

/-- `sufficientAt` and `causallySufficient` reduce to the same query (same
    `normalDevelopment` after Schulz/Fitting unification). -/
theorem CausalFrame.sufficientAt_iff_causallySufficient {W : Type}
    (f : CausalFrame W) (w : W) :
    f.sufficientAt w ↔
      causallySufficient f.dynamics (f.background w) f.trigger f.complement :=
  Iff.rfl

-- ════════════════════════════════════════════════════
-- § Ability Frame Constructor
-- ════════════════════════════════════════════════════

open Semantics.Attitudes.Intensional (World) in
/-- Construct an ability-modal `CausalFrame`: a world-indexed causal model
    where actualization is governed by aspect (not lexical assertion). -/
def abilityFrame (dynamics : CausalDynamics) (action complement : Variable)
    (background : World → Situation) : CausalFrame World :=
  { dynamics
    trigger := action
    complement
    background
    actualization := .aspectual }

open Semantics.Attitudes.Intensional (World) in
/-- `abilityFrame` always produces aspectual actualization. -/
theorem abilityFrame_aspectual (dyn : CausalDynamics) (act comp : Variable)
    (bg : World → Situation) :
    (abilityFrame dyn act comp bg).actualization = .aspectual := rfl

-- ════════════════════════════════════════════════════
-- § Ability-Specific Existence Theorems
-- ════════════════════════════════════════════════════

open Semantics.Attitudes.Intensional (World) in
/-- Ability differs from implicative verbs: ability can hold without
    actualization (impossible for *manage*). -/
theorem CausalFrame.ability_differs_from_implicative :
    ∃ (f : CausalFrame World) (w : World),
      f.actualization = .aspectual ∧
      ¬ (f.sufficientAt w ∧ f.actualizedAt w) := by
  let act := mkVar "act"
  let comp := mkVar "comp"
  let dyn := CausalDynamics.ofList [CausalLaw.simple act comp]
  let f := abilityFrame dyn act comp (λ _ => Situation.empty)
  exact ⟨f, .w0, rfl, by native_decide⟩

open Semantics.Attitudes.Intensional (World) in
/-- **Aspect governs actuality for ability**: the same ability frame
    yields different entailment patterns under different aspects. -/
theorem CausalFrame.aspect_governs_ability :
    ∃ (f : CausalFrame World) (w : World),
      f.actualization = .aspectual ∧
      f.actualityWithAspect .perfective w ∧
      f.actualizedAt w ∧
      ∃ w', f.actualityWithAspect .imperfective w' ∧
            ¬ f.actualizedAt w' := by
  let act := mkVar "act"
  let comp := mkVar "comp"
  let dyn := CausalDynamics.ofList [CausalLaw.simple act comp]
  let bg : World → Situation := λ w =>
    match w with
    | .w0 => Situation.empty.extend act true
    | _ => Situation.empty
  let f := abilityFrame dyn act comp bg
  exact ⟨f, .w0, rfl, by native_decide, by native_decide,
         .w1, by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § normalDevelopment growth (Fitting/Schulz info-extensivity)
-- ════════════════════════════════════════════════════

/-! `normalDevelopment` is info-extensive in the Schulz @cite{schulz-2011}
    sense: every truth in `s` is preserved (`s ⊑ normalDevelopment dyn s`
    in the truth-content order). It is NOT order-monotone in general
    (Schulz footnote 7), so it is not a `ClosureOperator` in mathlib's sense
    — only inflationary + idempotent without monotonicity-in-input. -/

/-- Inflationary: every truth in `s` is preserved by normal development. -/
theorem closure_inflationary (dyn : CausalDynamics) (s : Situation) :
    Situation.trueLE s (normalDevelopment dyn s) :=
  normalDevelopment_grows dyn s

-- ════════════════════════════════════════════════════
-- § Instance Bridge: Implicatives → CausalFrame
-- ════════════════════════════════════════════════════

open Semantics.Causation.Implicative in
/-- An `ImplicativeScenario` is a `CausalFrame Unit` with lexical actualization. -/
def CausalFrame.ofImplicative (sc : ImplicativeScenario) : CausalFrame Unit :=
  { dynamics := sc.dynamics
    trigger := sc.prerequisite
    complement := sc.complement
    background := λ _ => sc.background
    actualization := .lexical }

open Semantics.Causation.Implicative in
/-- The generic frame's sufficiency at `()` matches `manageSem`. -/
theorem implicative_sufficiency_matches (sc : ImplicativeScenario) :
    (CausalFrame.ofImplicative sc).sufficientAt () ↔
      causallySufficient sc.dynamics sc.background sc.prerequisite sc.complement :=
  Iff.rfl

end Semantics.Causation.ComplementEntailing

-- ════════════════════════════════════════════════════
-- § V2 namespace for new code
-- ════════════════════════════════════════════════════

/-! The legacy `manageSem` / `failSem` / `ImplicativeScenario` /
`PrerequisiteAccount` above remain on the `CausalDynamics` API for
backward compat with `Karttunen1971.lean`, `Nadathur2024.lean`, and
`Implicative.toSemantics` dispatch.

New consumers should `open Semantics.Causation.Implicative.V2` and use
the V2-flavored predicates which delegate to V2 `BoolSEM.causallySufficient`
(for `manageSem`) and V2 `BoolSEM.causallyNecessary` (for `prerequisite_necessary`,
when needed).

`ImplicativeScenario`-style struct ports deferred — V2 consumers can
call the predicates directly on their `BoolSEM`. -/

namespace Semantics.Causation.Implicative.V2

open Core.Causal.V2 (BoolSEM CausalGraph Valuation)

/-- V2 manage-sem: prerequisite is causally sufficient for complement. -/
abbrev manageSem {V : Type*} [Fintype V] [DecidableEq V]
    (M : BoolSEM V) [CausalGraph.IsDAG M.graph] [Core.Causal.V2.SEM.IsDeterministic M]
    (background : Valuation (fun _ : V => Bool))
    (prerequisite complement : V) : Prop :=
  Core.Causal.V2.BoolSEM.causallySufficient M background prerequisite complement

/-- V2 fail-sem: prerequisite is NOT causally sufficient for complement. -/
abbrev failSem {V : Type*} [Fintype V] [DecidableEq V]
    (M : BoolSEM V) [CausalGraph.IsDAG M.graph] [Core.Causal.V2.SEM.IsDeterministic M]
    (background : Valuation (fun _ : V => Bool))
    (prerequisite complement : V) : Prop :=
  ¬ manageSem M background prerequisite complement

/-- V2 necessity presupposition: prerequisite is causally necessary
    (Nadathur 2024 Def 10b) for complement. -/
abbrev necessityPresup {V : Type*} [Fintype V] [DecidableEq V]
    (M : BoolSEM V) [CausalGraph.IsDAG M.graph] [Core.Causal.V2.SEM.IsDeterministic M]
    (background : Valuation (fun _ : V => Bool))
    (prerequisite complement : V) : Prop :=
  Core.Causal.V2.BoolSEM.causallyNecessary M background prerequisite complement

end Semantics.Causation.Implicative.V2
