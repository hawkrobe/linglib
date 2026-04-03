import Linglib.Core.StructuralEquationModel
import Linglib.Theories.Semantics.Causation.Sufficiency

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

namespace Nadathur2024.Implicative

open Core.StructuralEquationModel

-- ════════════════════════════════════════════════════
-- § Prerequisite Types (@cite{nadathur-2024} §2, §5.2)
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
def manageSem (sc : ImplicativeScenario) : Bool :=
  causallySufficient sc.dynamics sc.background sc.prerequisite sc.complement

/-- Semantics of "fail": the complement did NOT develop.

    "Kim failed to swim across" entails "Kim did not swim across."
    Dual of `manageSem`: `failSem sc = !manageSem sc`. -/
def failSem (sc : ImplicativeScenario) : Bool :=
  !manageSem sc

/-- **Central grounding theorem**: if `manageSem` holds, the complement
    is true after normal development.

    This grounds `VerbEntry.implicativeBuilder := some.positive` for *manage*:
    the entailment is not stipulated but follows from causal sufficiency. -/
theorem manage_entails_complement (sc : ImplicativeScenario)
    (h : manageSem sc = true) :
    (normalDevelopment sc.dynamics (sc.background.extend sc.prerequisite true)).hasValue
      sc.complement true = true := h

/-- If `failSem` holds, the complement is false after normal development. -/
theorem fail_entails_not_complement (sc : ImplicativeScenario)
    (h : failSem sc = true) :
    (normalDevelopment sc.dynamics (sc.background.extend sc.prerequisite true)).hasValue
      sc.complement true = false := by
  simp only [failSem, manageSem, causallySufficient, Bool.not_eq_true'] at h
  exact h

/-- Implicative entailment is NOT aspect-governed: the entailment holds with
    no aspect parameter in the semantics. This contrasts with ability modals
    (see `Modal/Ability.lean`) where aspect determines whether the complement
    is entailed. -/
theorem implicative_not_aspect_governed (sc : ImplicativeScenario)
    (h : manageSem sc = true) :
    (normalDevelopment sc.dynamics (sc.background.extend sc.prerequisite true)).hasValue
      sc.complement true = true :=
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
def PrerequisiteAccount.necessityPresup (pa : PrerequisiteAccount) : Bool :=
  causallyNecessary pa.dynamics pa.background pa.prereqVar pa.complementVar

/-- (32iii): **Check** whether A(x) is causally sufficient for P(x) in
    the model. This is a computed property of the dynamics/background,
    distinct from `hasSufficiencyPresup` (a lexical property of the verb).
    For well-formed accounts, `sufficiencyPresup = hasSufficiencyPresup`. -/
def PrerequisiteAccount.sufficiencyPresup (pa : PrerequisiteAccount) : Bool :=
  causallySufficient pa.dynamics pa.background pa.prereqVar pa.complementVar

/-- (32ii): The assertion — A(x) holds in the evaluation world. -/
def PrerequisiteAccount.assertion (pa : PrerequisiteAccount) (w : Situation) : Bool :=
  w.hasValue pa.prereqVar true

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
    (hSuf : pa.sufficiencyPresup = true) :
    manageSem pa.toScenario = true := hSuf

-- ════════════════════════════════════════════════════
-- § Directionality
-- ════════════════════════════════════════════════════

/-- Directionality of complement entailment (@cite{nadathur-2024} §6.3).

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
theorem manage_swim_holds : manageSem manageScenario = true := by native_decide

/-- Concrete verification: the complement (swimming across) is true. -/
theorem manage_swim_complement_true :
    (normalDevelopment manageScenario.dynamics
      (manageScenario.background.extend manageScenario.prerequisite true)).hasValue
      manageScenario.complement true = true := by native_decide

/-- The fail scenario: same dynamics, but testing failSem.
    If the dynamics DO fire (prerequisite sufficient for complement), failSem is false. -/
theorem fail_swim_false_when_sufficient :
    failSem manageScenario = false := by native_decide

/-- A scenario where the prerequisite is NOT sufficient (no causal law). -/
private def failScenario : ImplicativeScenario where
  dynamics := CausalDynamics.empty  -- no law connecting prerequisite to complement
  prerequisite := tryAction
  complement := swimAcross
  background := Situation.empty

/-- When there's no causal connection, failSem holds (complement doesn't develop). -/
theorem fail_no_law_holds : failSem failScenario = true := by native_decide

end ConcreteExample

-- ════════════════════════════════════════════════════
-- § ImplicativeBuilder: Enum basis for Fragment entries
-- ════════════════════════════════════════════════════

/-- Builder enum for implicative verbs, following the `CausativeBuilder` pattern.

    Positive implicatives (*manage*, *remember*) entail the complement on success.
    Negative implicatives (*fail*, *forget*) entail the complement does NOT hold on success.

    Note: `ImplicativeBuilder` and `CausativeBuilder` are structurally different
    (@cite{nadathur-2024}): causatives directly predicate causation (make/cause →
    sufficiency/necessity), while implicatives predicate a prerequisite whose
    causal relationship to the complement is only presupposed. -/
inductive ImplicativeBuilder where
  | positive   -- manage, remember: success → complement true
  | negative   -- fail, forget: success → complement NOT true
  deriving DecidableEq, Repr

/-- Whether the builder entails the complement (positive) or its negation (negative). -/
def ImplicativeBuilder.entailsComplement : ImplicativeBuilder → Bool
  | .positive => true
  | .negative => false

/-- Map to the compositional semantics (`manageSem` or `failSem`). -/
def ImplicativeBuilder.toSemantics : ImplicativeBuilder →
    (ImplicativeScenario → Bool)
  | .positive => manageSem
  | .negative => failSem

/-- Positive builder entails complement: if `manageSem` holds, complement is true. -/
theorem positive_entails_complement (sc : ImplicativeScenario)
    (h : ImplicativeBuilder.positive.toSemantics sc = true) :
    (normalDevelopment sc.dynamics (sc.background.extend sc.prerequisite true)).hasValue
      sc.complement true = true :=
  manage_entails_complement sc h

/-- Negative builder entails NOT complement: if `failSem` holds, complement is false. -/
theorem negative_entails_not_complement (sc : ImplicativeScenario)
    (h : ImplicativeBuilder.negative.toSemantics sc = true) :
    (normalDevelopment sc.dynamics (sc.background.extend sc.prerequisite true)).hasValue
      sc.complement true = false :=
  fail_entails_not_complement sc h

/-- `entailsComplement` matches semantic behavior: positive ↔ `manageSem`,
    negative ↔ `failSem`. -/
theorem entailsComplement_positive :
    ImplicativeBuilder.positive.entailsComplement = true := rfl

theorem entailsComplement_negative :
    ImplicativeBuilder.negative.entailsComplement = false := rfl

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
      (@cite{nadathur-2024} §5.2) -/
structure ImplicativeClass where
  /-- Positive (manage, force) or negative (fail, prevent) polarity -/
  polarity : ImplicativeBuilder
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
    (@cite{nadathur-2024} §6.4) -/
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
    (polarity : ImplicativeBuilder) : ImplicativeClass :=
  { polarity := polarity
    directionality := pa.directionality
    aspectGoverned := false
    prerequisite := some pa.prerequisiteType }

end Nadathur2024.Implicative
