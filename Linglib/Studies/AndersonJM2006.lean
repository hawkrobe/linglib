import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Lattice.Fold
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.DeriveFintype
import Linglib.Features.Case.Basic
import Linglib.Features.Case.Basic
import Linglib.Semantics.ArgumentStructure.EntailmentProfile
import Linglib.Semantics.ArgumentStructure.Linking
import Linglib.Fragments.English.Predicates.Verbal
import Linglib.Semantics.Verb.Denotation

/-!
# Anderson (2006): Modern Grammars of Case [anderson-jm-2006]

[anderson-jm-2006] "Modern Grammars of Case: A Retrospective" (OUP)
develops localist case grammar (LCG), where all semantic relations decompose
into combinations of three first-order case features: absolutive (abs),
source/ergative (src), and locative (loc).

## Anderson's system (Ch. 6, eq. 11)

The four simple case relations are:
- **abs** (∅): the semantically empty base — holistic participant
- **source/erg** ({src}): first-order source — agent, causer
- **loc** ({loc}): place/location
- **abl** ({loc, src²}): second-order source subordinated to loc

Arguments bear COMBINATIONS of first-order features to define complex
roles (§6.2–6.3):
- Agent = src alone ("Bill read the book", eq. 39a)
- Experiencer = src + loc ("Bill knew the answer", eq. 39h)
- Contactive/patient = abs + loc (eq. 22)
- Self-mover = abs + src ("Bill flew to China", eq. 39c)

## Subject selection (eq. 38')

Anderson directly states: **erg > abs**. The argument with first-order
source becomes subject. If no argument has source, the absolutive
becomes subject. The hierarchy is NOT derived from feature cardinality.

Subject formation (eq. 40): absolutive ⇒ absolutive{erg}. When an
absolutive is selected as subject, it acquires the erg feature.

## Improvement over the two-feature model

Our earlier formalization incorrectly used only two features (abs, erg)
and collapsed experiencer with agent as {abs, erg}. Anderson's actual
system DISTINGUISHES them: agent = {src}, experiencer = {src, loc}.
Both have src (so both can be subjects), but they differ in the loc
feature. The third feature (loc) is essential to Anderson's theory.

## Costs

The three-feature system collapses some Fragment distinctions:
- {src} collapses **agent**, **source**, **instrument**, **stimulus**
- {abs} collapses **patient** and **theme**
But it correctly distinguishes experiencer from agent (unlike the
two-feature simplification).
-/

namespace AndersonJM2006

open Semantics.ArgumentStructure.Linking (LinkingTheory ArgPosition)
open ArgumentStructure.EntailmentProfile
open English.Predicates.Verbal

-- ============================================================================
-- § 0: Anderson's Case Features — Substrate
-- ============================================================================

/-! Three first-order case features `[abs, src, loc]`, the 8 case relations
that arise as their feature bundles, the subject-selection hierarchy over
those bundles, predicate scenarios (argument-structure tuples of relations),
and the morphological-case → relation map. Originally landed as standalone
substrate in `Features/Case/Basic.lean`; inlined here because only this
study consumes it. -/

/-- Anderson's three first-order case features (Ch. 6). -/
inductive CaseFeature where
  | abs
  | src
  | loc
  deriving DecidableEq, Repr, Fintype

/-- An argument's case specification: a bundle of first-order features (Ch. 6).

    A `CaseRelation` is a `Finset CaseFeature` — the powerset of the three
    primitive features. The 8 possible bundles are exactly `Finset.powerset`
    of `Finset.univ`. Containment (`⊆`), the empty bundle (`∅`), the full
    bundle (`Finset.univ`), and meet/join are inherited from `Finset`'s
    `BooleanAlgebra` instance. -/
abbrev CaseRelation := Finset CaseFeature

namespace CaseRelation

@[reducible] def neutral    : CaseRelation := ∅
@[reducible] def absolutive : CaseRelation := {.abs}
@[reducible] def ergative   : CaseRelation := {.src}
@[reducible] def locative   : CaseRelation := {.loc}
@[reducible] def srcAbs     : CaseRelation := {.abs, .src}
@[reducible] def srcLoc     : CaseRelation := {.src, .loc}
@[reducible] def absLoc     : CaseRelation := {.abs, .loc}
@[reducible] def absSrcLoc  : CaseRelation := {.abs, .src, .loc}

/-- The full feature set is `Finset.univ` and equals the 3-feature top. -/
theorem absSrcLoc_eq_univ :
    absSrcLoc = (Finset.univ : Finset CaseFeature) := by decide

/-- Convenience accessors for the three features. -/
@[reducible] def abs (cr : CaseRelation) : Prop := .abs ∈ cr
@[reducible] def src (cr : CaseRelation) : Prop := .src ∈ cr
@[reducible] def loc (cr : CaseRelation) : Prop := .loc ∈ cr

end CaseRelation

/-- The subject selection rank (eq. 38').
    src (agent) outranks abs (patient) outranks loc (spatial).

    Codomain `Fin 3` — three tiers, type-level boundedness. -/
def CaseRelation.subjectRank (cr : CaseRelation) : Fin 3 :=
  if .src ∈ cr then 2 else if .abs ∈ cr then 1 else 0

/-- The `src` feature alone determines subject rank 2 — regardless of other
    features. This is why ergative, experiencer (srcLoc), and self-mover
    (srcAbs) all tie for highest subject rank. -/
theorem src_determines_subject_rank (cr : CaseRelation) (h : .src ∈ cr) :
    cr.subjectRank = 2 := by simp [CaseRelation.subjectRank, h]

/-- Without `src`, the `abs` feature determines rank 1. This is why
    absolutive and contactive (absLoc) tie at the second tier. -/
theorem abs_without_src_rank (cr : CaseRelation)
    (h1 : .src ∉ cr) (h2 : .abs ∈ cr) :
    cr.subjectRank = 1 := by simp [CaseRelation.subjectRank, h1, h2]

/-- Anderson's `absSrcLoc` is the top of the feature lattice. -/
theorem absSrcLoc_is_top (cr : CaseRelation) :
    cr ⊆ CaseRelation.absSrcLoc := by
  rw [CaseRelation.absSrcLoc_eq_univ]; exact Finset.subset_univ cr

/-- Anderson's `neutral` (the empty bundle) is the bottom of the feature
    lattice. -/
theorem neutral_is_bottom (cr : CaseRelation) : CaseRelation.neutral ⊆ cr :=
  Finset.empty_subset cr

/-- The 8 possible case relations are exactly
    `(Finset.univ : Finset CaseFeature).powerset`.
    Cardinality follows from `Finset.card_powerset`. -/
theorem CaseRelation.card_all :
    (Finset.univ : Finset CaseFeature).powerset.card = 8 := by decide

/-- A predicate's **scenario** (Ch. 6): the case relations assigned to its
    arguments. -/
structure Scenario where
  relations : List CaseRelation

def Scenario.arity (s : Scenario) : Nat := s.relations.length

def Scenario.subjectRelation (s : Scenario) : Option CaseRelation :=
  s.relations.head?

def Scenario.objectRelation (s : Scenario) : Option CaseRelation :=
  match s.relations with
  | _ :: cr :: _ => some cr
  | _ => none

def Scenario.transitive   : Scenario := ⟨[.ergative, .absolutive]⟩
def Scenario.unergative   : Scenario := ⟨[.ergative]⟩
def Scenario.unaccusative : Scenario := ⟨[.absolutive, .locative]⟩
def Scenario.selfMoving   : Scenario := ⟨[.srcAbs, .locative]⟩
def Scenario.experiencer  : Scenario := ⟨[.srcLoc, .absolutive]⟩

theorem transitive_subject_object :
    Scenario.transitive.subjectRelation = some .ergative ∧
    Scenario.transitive.objectRelation = some .absolutive := ⟨rfl, rfl⟩

theorem unergative_subject_only :
    Scenario.unergative.subjectRelation = some .ergative ∧
    Scenario.unergative.objectRelation = none := ⟨rfl, rfl⟩

theorem unaccusative_subject_loc :
    Scenario.unaccusative.subjectRelation = some .absolutive ∧
    Scenario.unaccusative.objectRelation = some .locative := ⟨rfl, rfl⟩

theorem selfMoving_subject :
    Scenario.selfMoving.subjectRelation = some .srcAbs ∧
    Scenario.selfMoving.objectRelation = some .locative := ⟨rfl, rfl⟩

theorem experiencer_subject_object :
    Scenario.experiencer.subjectRelation = some .srcLoc ∧
    Scenario.experiencer.objectRelation = some .absolutive := ⟨rfl, rfl⟩

theorem transitive_subject_outranks_object :
    CaseRelation.ergative.subjectRank > CaseRelation.absolutive.subjectRank := by
  decide

theorem unergative_unaccusative_differ :
    Scenario.unergative.subjectRelation ≠
    Scenario.unaccusative.subjectRelation := by decide

end AndersonJM2006

/-! Anderson's `Case → CaseRelation` map lives under `namespace Syntax` so
it can be invoked via dot-notation on `c : Case` (mirroring how
`Case.hierarchyRank` and the Caha containment defs project onto
the type). -/
/-- Canonical mapping from Blake's morphological cases to Anderson's
    case-feature bundles (Ch. 6). -/
def Case.toCaseRelation : Case → Option AndersonJM2006.CaseRelation
  | .nom  => some .srcAbs
  | .acc  => some .absolutive
  | .erg  => some .srcAbs
  | .abs  => some .absolutive
  | .abl  => some .locative
  | .loc  => some .locative
  | .inst => some .ergative
  | _     => none

theorem Case.nom_erg_same_relation :
    Case.toCaseRelation .nom = Case.toCaseRelation .erg := rfl

theorem Case.acc_abs_same_relation :
    Case.toCaseRelation .acc = Case.toCaseRelation .abs := rfl

namespace AndersonJM2006

open Semantics.ArgumentStructure.Linking (LinkingTheory ArgPosition)
open ArgumentStructure.EntailmentProfile
open English.Predicates.Verbal

-- ============================================================================
-- § 1: Mappings Between Case Relations and Theta Roles
-- ============================================================================

/-- Anderson's canonical mapping from case-feature bundles to theta roles.

    The three-feature system makes finer distinctions than the old
    two-feature version: experiencer ({src, loc}) is now SEPARATE from
    agent ({src}). -/
def CaseRelation.canonicalTheta (cr : CaseRelation) : Option ThetaRole :=
  if CaseFeature.src ∈ cr then
    if CaseFeature.loc ∈ cr then some .experiencer  -- srcLoc, absSrcLoc
    else some .agent                                 -- ergative, srcAbs
  else if CaseFeature.abs ∈ cr then some .patient   -- absolutive, absLoc
  else none                                          -- neutral, locative

/-- Reverse mapping: from the Fragment's 8-role inventory to Anderson's
    case relations.

    Key differences from the old two-feature mapping:
    - experiencer → srcLoc (was absErg, same as agent)
    - agent → ergative (was absErg, conflated with experiencer)
    - goal → locative (spatial goal = loc{goal})

    The many-to-one collapses that remain:
    - agent, source, instrument, stimulus → ergative {src}
    - patient, theme → absolutive {abs} -/
def thetaToCaseRelation : ThetaRole → CaseRelation
  | .agent       => .ergative    -- src: non-locational source of action
  | .experiencer => .srcLoc      -- src + loc: locative source (E = erg,loc)
  | .patient     => .absolutive  -- abs: affected entity
  | .theme       => .absolutive  -- abs: entity in motion/state
  | .goal        => .locative    -- loc: spatial goal (loc{goal} in full system)
  | .source      => .ergative    -- src: source (Anderson unifies with agent)
  | .instrument  => .ergative    -- src: source of force
  | .stimulus    => .ergative    -- src: cause of experience

-- ============================================================================
-- § 2: Anderson's Derivations (eq. 39)
-- ============================================================================

/-! Anderson's derivations from Chapter 6 (eq. 39) show how the
three-feature system assigns case relations to English verb arguments.
For each verb, the subject is the argument with the highest subjectRank. -/

/-- Eq. 39a: "Bill read the book" — erg + abs.
    Agent (src, rank 2) + patient (abs, rank 1). Agent is subject. -/
theorem read_derivation :
    let agent := CaseRelation.ergative
    let patient := CaseRelation.absolutive
    agent.subjectRank > patient.subjectRank := by decide

/-- Eq. 39b: "Bill fell to the ground" — abs + loc{goal}.
    Theme (abs, rank 1) + locative goal (loc, rank 0). Theme is subject. -/
theorem fell_derivation :
    let theme := CaseRelation.absolutive
    let goal := CaseRelation.locative
    theme.subjectRank > goal.subjectRank := by decide

/-- Eq. 39c: "Bill flew to China" — abs,erg + loc{goal}.
    Self-mover (abs+src, rank 2) + goal (loc, rank 0). Self-mover is subject. -/
theorem flew_derivation :
    let selfMover := CaseRelation.srcAbs
    let goal := CaseRelation.locative
    selfMover.subjectRank > goal.subjectRank := by decide

/-- Eq. 39h: "Bill knew the answer" — E + abs = erg,loc + abs.
    Experiencer (src+loc, rank 2) + stimulus (abs, rank 1).
    Experiencer is subject because it has src. -/
theorem knew_derivation :
    let experiencer := CaseRelation.srcLoc
    let stimulus := CaseRelation.absolutive
    experiencer.subjectRank > stimulus.subjectRank := by decide

/-- Anderson's key distinction: experiencer ≠ agent in feature content,
    but BOTH outrank absolutive. Agent = {src}, experiencer = {src, loc}.
    The loc feature distinguishes them without affecting subject selection. -/
theorem experiencer_agent_distinct_same_rank :
    CaseRelation.srcLoc ≠ CaseRelation.ergative ∧
    CaseRelation.srcLoc.subjectRank = CaseRelation.ergative.subjectRank := by
  exact ⟨by decide, rfl⟩

-- ============================================================================
-- § 3: Verb → Scenario (End-to-End Bridge)
-- ============================================================================

/-- Derive Anderson's `Scenario` from a Fragment verb entry's derived roles
    (`Verb.subjectRole`/`objectRole`, the canonical theta-grid). -/
def toScenario (v : Verb) : Scenario :=
  ⟨(v.subjectRole |>.map thetaToCaseRelation).toList ++
   (v.objectRole |>.map thetaToCaseRelation).toList⟩

-- ============================================================================
-- § 4: Anderson as LinkingTheory
-- ============================================================================

/-- Anderson's case grammar as a `LinkingTheory` ([anderson-jm-2006]).
    The verb type is `Scenario`, the context is `Unit` (lexicalist: linking
    is derived entirely from case-relation rank, no structural input). -/
def andersonLinking : LinkingTheory Scenario Unit where
  compatible := λ _ => [()]
  predict := λ scenario () pos =>
    match pos with
    | .subject      => scenario.subjectRelation.bind CaseRelation.canonicalTheta
    | .directObject => scenario.objectRelation.bind CaseRelation.canonicalTheta
    | _             => none

/-- Anderson's predicted subject theta role for a verb entry. -/
def andersonPredictedSubjectTheta (v : Verb) : Option ThetaRole :=
  andersonLinking.predict (toScenario v) () .subject

-- ============================================================================
-- § 5: Linking Predictions — Canonical Verb Types
-- ============================================================================

/-- Anderson correctly predicts argument linking for the canonical
    verb types, including experiencer (which the old two-feature model
    collapsed with agent). -/
theorem anderson_canonical_linking :
    andersonLinking.predict .transitive () .subject = some .agent ∧
    andersonLinking.predict .transitive () .directObject = some .patient ∧
    andersonLinking.predict .unergative () .subject = some .agent ∧
    andersonLinking.predict .unaccusative () .subject = some .patient ∧
    andersonLinking.predict .experiencer () .subject = some .experiencer ∧
    andersonLinking.predict .experiencer () .directObject = some .patient :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- The three-feature system correctly predicts experiencer as subject,
    which the old two-feature system collapsed into agent. -/
theorem experiencer_correctly_predicted :
    andersonLinking.predict .experiencer () .subject = some .experiencer := rfl

-- ============================================================================
-- § 6: Linking Accuracy Against the Fragment Lexicon
-- ============================================================================

/-- Anderson correctly predicts which argument becomes subject for
    every verb in the Fragment: the prediction is defined iff the
    verb has a derived subject role. -/
theorem anderson_linking_accuracy :
    (allVerbs.filter λ v =>
      (andersonPredictedSubjectTheta v.toVerb).isSome ==
      (v.toVerb.subjectRole).isSome).length = allVerbs.length := by
  native_decide

-- ============================================================================
-- § 7: Role Collapses — What Anderson's Three-Feature System Costs
-- ============================================================================

/-! The three-feature system collapses fewer roles than the old
two-feature model. Experiencer is now correctly distinguished from
agent. The remaining collapses are:
- {src} collapses agent with source, instrument, and stimulus
- {abs} collapses patient with theme -/

-- § 7a: {abs} collapses patient and theme

/-- Patient and theme both map to {abs}, but [dowty-1991] distinguishes
    them: patient has 3 P-Patient entailments, theme has only 1. -/
theorem patient_theme_collapse :
    thetaToCaseRelation .patient = thetaToCaseRelation .theme ∧
    (ThetaRole.canonicalProfile .patient).pPatientScore = 3 ∧
    (ThetaRole.canonicalProfile .theme).pPatientScore = 1 := by
  exact ⟨rfl, by native_decide, by native_decide⟩

-- § 7b: {src} collapses agent, source, instrument, stimulus

/-- Agent, source, instrument, and stimulus all map to {src}. -/
theorem src_collapses :
    thetaToCaseRelation .agent = thetaToCaseRelation .source ∧
    thetaToCaseRelation .agent = thetaToCaseRelation .instrument ∧
    thetaToCaseRelation .agent = thetaToCaseRelation .stimulus := ⟨rfl, rfl, rfl⟩

-- § 7c: Experiencer is NOW correctly distinguished

/-- The three-feature system correctly separates experiencer from agent.
    This is the key improvement over the old two-feature formalization. -/
theorem experiencer_distinguished :
    thetaToCaseRelation .agent ≠ thetaToCaseRelation .experiencer := by decide

/-- Experiencer subject verbs are now correctly predicted as experiencer,
    not collapsed into agent (for verbs with entailment profiles). -/
theorem experiencer_verbs_correct :
    (allVerbs.filter λ v =>
      (v.toVerb.subjectRole) == some .experiencer ∧
      andersonPredictedSubjectTheta v.toVerb == some .experiencer).length =
    (allVerbs.filter λ v =>
      (v.toVerb.subjectRole) == some .experiencer).length := by
  native_decide

-- ============================================================================
-- § 8: Bridge to Blake's Hierarchy
-- ============================================================================

/-- Anderson and Blake are concordant on the core case ordering.
    Blake: NOM(6) ≥ ACC(6). Anderson: NOM/src+abs outranks ACC/abs
    (subjectRank 2 > 1). Both are inverse to Caha's containment
    hierarchy. -/
theorem anderson_blake_concordant :
    Case.hierarchyRank .nom ≥ Case.hierarchyRank .acc ∧
    CaseRelation.srcAbs.subjectRank > CaseRelation.absolutive.subjectRank ∧
    Case.hierarchyRank .nom = Case.hierarchyRank .acc ∧
    CaseRelation.srcAbs.subjectRank ≠ CaseRelation.absolutive.subjectRank := by
  exact ⟨by decide, by decide, rfl, by decide⟩

-- ============================================================================
-- § 9: Localist Hypothesis — Spatial Cases Share {loc}
-- ============================================================================

/-- Does a morphological case carry the spatial locative feature?
    ABL, LOC both map to {loc} — they share the locative feature
    because they involve spatial location. -/
def HasSpatialLoc : Case → Prop
  | .abl  => True
  | .loc  => True
  | _     => False

instance : DecidablePred HasSpatialLoc := fun c => by
  cases c <;> unfold HasSpatialLoc <;> infer_instance

/-- ABL and LOC both map to Anderson's locative case relation. -/
theorem spatial_cases_are_locative :
    Case.toCaseRelation .abl = some .locative ∧
    Case.toCaseRelation .loc = some .locative := ⟨rfl, rfl⟩

/-- INST maps to {src} (source of force), not {loc}. Anderson argues
    that instrumental is the same semantic relation as agent: both are
    sources of action. -/
theorem inst_is_ergative :
    Case.toCaseRelation .inst = some .ergative := rfl

/-- ABL and LOC share a case relation AND have an extension path
    between them. Anderson's explanation: a case marker conditioned
    on {loc} is polysemous across spatial functions. -/
theorem abl_loc_share_feature :
    Case.toCaseRelation .abl = Case.toCaseRelation .loc := rfl

-- ============================================================================
-- § 10: NOM/ERG and ACC/ABS Unification
-- ============================================================================

/-- Accusative and ergative alignment are different morphological labels
    for the same two case relations:
    NOM = ERG = src+abs,  ACC = ABS = abs.
    The case relations are identical; alignment is labeling. -/
theorem alignment_is_labeling :
    Case.toCaseRelation .nom = Case.toCaseRelation .erg ∧
    Case.toCaseRelation .acc = Case.toCaseRelation .abs ∧
    Case.toCaseRelation .nom ≠ Case.toCaseRelation .acc := by
  exact ⟨rfl, rfl, by decide⟩

-- ============================================================================
-- § 11: Bridge to Dowty's Proto-Roles
-- ============================================================================

/-- Anderson and Dowty agree on transitive linking despite completely
    different primitives (features vs entailment profiles). -/
theorem anderson_dowty_transitive_agree :
    CaseRelation.canonicalTheta .ergative = some .agent ∧
    CaseRelation.canonicalTheta .absolutive = some .patient ∧
    OutranksForSubject
      (ThetaRole.canonicalProfile .agent)
      (ThetaRole.canonicalProfile .patient) := by
  exact ⟨rfl, rfl, by decide⟩

/-- The three-feature system improves on the old two-feature version
    for the experiencer case: Anderson distinguishes experiencer from
    agent (via loc), as does Dowty (different P-Agent entailment count). -/
theorem anderson_dowty_experiencer_agree :
    -- Anderson: different case relations
    thetaToCaseRelation .agent ≠ thetaToCaseRelation .experiencer ∧
    -- Dowty: different entailment profiles
    (ThetaRole.canonicalProfile .agent).pAgentScore >
    (ThetaRole.canonicalProfile .experiencer).pAgentScore := by
  exact ⟨by decide, by native_decide⟩

end AndersonJM2006
