import Linglib.Semantics.ArgumentStructure.AgentivityLattice
import Linglib.Semantics.ArgumentStructure.EntailmentProfile
import Linglib.Studies.Aissen2003

/-!
# [grimm-2011]: Semantics of Case — Lattice Predictions
[grimm-2011] [aissen-2003] [von-heusinger-2008]

Study file connecting [grimm-2011]'s agentivity lattice
(`Semantics/Events/AgentivityLattice.lean`) to the differential
object marking profiles in `Studies/Aissen2003.lean`.

## Key results

1. **Russian DOM matches the lattice exactly**: for canonical transitives
   (quPersBeginning), `DomPredictedByLattice` holds for exactly
   {animate, human} — the same cells Russian marks.

2. **Spanish DOM is a proper subset**: the lattice predicts DOM for
   {animate, human}, but Spanish only marks {human}.

3. **Two frameworks, same predictions**: the lattice-derived DOM is
   always monotone in [aissen-2003]'s sense, and the lattice's
   canonical transitive prediction exactly matches Aissen's OT Type 2.

4. **Full case region table**: every canonical verb is mapped through
   the lattice to a case region, connecting argument selection to
   morphological case.

5. **Verb class effect**: the lattice predicts that creation verb objects
   are entirely outside the transitivity region (DOM inapplicable), while
   contact and consumption verbs have objects in the canonical patient
   region. This connects to [von-heusinger-2008]'s observation that
   DOM regularized earliest for agent-patient verbs.
-/

namespace Grimm2011

open Semantics.ArgumentStructure.AgentivityLattice
open Semantics.ArgumentStructure.EntailmentProfile
open Features.Prominence
open Aissen2003

-- ════════════════════════════════════════════════════
-- § 0. DOM Substrate: animacy → agentivity, DOM predicate
-- ════════════════════════════════════════════════════

/-! [grimm-2011] p.534: "it is a combination of verbal and nominal
    properties which trigger DOM." This substrate maps nominal animacy to
    a baseline agentive position on the lattice, combines it with verbal
    persistence to predict a case region, and packages the residual
    "object outside ACC/ABS" condition as `DomPredictedByLattice`. -/

-- ── §0.1 Animacy → agentivity mapping ──

/-- Map nominal animacy to baseline agentive capacity on the lattice.

    Only *inherent* referent properties are mapped — not event-specific
    ones like instigation or motion:

    - Human: volition + sentience (capacity for intentional action)
    - Animate: sentience (conscious but non-volitional)
    - Inanimate: ⊥ (no inherent agentive capacity)

    The exclusion of instigation and motion is principled: these are
    event properties (did the participant instigate THIS event? move
    during THIS event?), not referent properties. Volition and sentience
    are inherent capacities of the referent type. -/
def animacyToAgentivity : AnimacyLevel → AgentivityNode
  | .human     => ⟨true, true, false, false⟩   -- {V, S}
  | .animate   => ⟨false, true, false, false⟩  -- {S}
  | .inanimate => ⊥

/-- All animacy-derived nodes satisfy volition → sentience. -/
theorem animacy_all_valid (a : AnimacyLevel) :
    (animacyToAgentivity a).Valid := by
  cases a <;> decide

/-- The mapping is monotone: higher animacy → higher agentivity.
    This is a structural property of the feature-subset ordering,
    not a stipulation. -/
theorem animacy_agentivity_monotone :
    animacyToAgentivity .inanimate ≤ animacyToAgentivity .animate ∧
    animacyToAgentivity .animate ≤ animacyToAgentivity .human := by
  constructor <;> decide

-- ── §0.2 Object node from animacy × verb persistence ──

/-- Combine a referent's nominal agentivity (from animacy) with the
    verb's persistence profile for the object. -/
def objectNodeWithAnimacy (animacy : AnimacyLevel)
    (verbPersistence : PersistenceLevel) : GrimmNode :=
  ⟨animacyToAgentivity animacy, verbPersistence⟩

/-- **The key non-circular derivation.** For canonical transitive objects
    (quPersBeginning = contact verbs like kick, hit, push):

    - Inanimate: `⟨⊥, qPB⟩` → `toCaseRegion` = **accAbs**
      (prototypical patient, no DOM needed)
    - Animate: `⟨{S}, qPB⟩` → `toCaseRegion` = **dative**
      (sentience shifts it into the dative region, Fig. 7)
    - Human: `⟨{V,S}, qPB⟩` → `toCaseRegion` = **dative**
      (volition + sentience, also in dative region)

    `toCaseRegion` is defined in the substrate for general case theory,
    not for DOM. That it automatically separates inanimate objects (accAbs)
    from animate/human objects (dative) is the lattice's genuine prediction. -/
theorem inanimate_object_in_accAbs :
    (objectNodeWithAnimacy .inanimate .quPersBeginning).toCaseRegion
    = .accAbs := by decide

theorem animate_object_in_dative :
    (objectNodeWithAnimacy .animate .quPersBeginning).toCaseRegion
    = .dative := by decide

theorem human_object_in_dative :
    (objectNodeWithAnimacy .human .quPersBeginning).toCaseRegion
    = .dative := by decide

-- ── §0.3 DOM predicate: object in transitivity region but outside ACC/ABS ──

/-- DOM is predicted when the object is in the transitivity region
    but its nominal agentivity pushes it outside the ACC/ABS case
    region. Both conditions use infrastructure defined for general
    case theory, not for DOM. -/
def DomPredictedByLattice (animacy : AnimacyLevel)
    (verbPersistence : PersistenceLevel) : Prop :=
  let node := objectNodeWithAnimacy animacy verbPersistence
  node.InTransitiveRegion ∧ node.toCaseRegion ≠ .accAbs

instance (a : AnimacyLevel) (p : PersistenceLevel) :
    Decidable (DomPredictedByLattice a p) := by
  unfold DomPredictedByLattice; infer_instance

/-- Inanimate objects of canonical transitives: in ACC/ABS, no DOM. -/
theorem inanimate_canonical_no_dom :
    ¬ DomPredictedByLattice .inanimate .quPersBeginning := by
  decide

/-- Animate objects of canonical transitives: outside ACC/ABS, DOM
    predicted. The lattice reason: sentience pushes the object into
    the dative region (Fig. 7). -/
theorem animate_canonical_dom :
    DomPredictedByLattice .animate .quPersBeginning := by
  decide

/-- Human objects: also outside ACC/ABS, DOM predicted. -/
theorem human_canonical_dom :
    DomPredictedByLattice .human .quPersBeginning := by
  decide

-- ── §0.4 Resultative transitives (exPersBeginning) ──

/-- The same pattern holds for resultative verbs (break, destroy):
    inanimate objects stay in ACC/ABS, animate/human objects do not. -/
theorem inanimate_resultative_no_dom :
    ¬ DomPredictedByLattice .inanimate .exPersBeginning := by
  decide

theorem animate_resultative_dom :
    DomPredictedByLattice .animate .exPersBeginning ∧
    DomPredictedByLattice .human .exPersBeginning :=
  ⟨by decide, by decide⟩

-- ── §0.5 Creation verbs: outside transitivity entirely ──

/-- Creation verb objects (build, invent — exPersEnd) are outside the
    transitivity region at ALL animacy levels. The object does not
    exist at event start, so it cannot "intrude" on the agent's role.
    DOM is inapplicable, not merely unnecessary. -/
theorem creation_outside_transitivity (a : AnimacyLevel) :
    ¬ (objectNodeWithAnimacy a .exPersEnd).InTransitiveRegion := by
  cases a <;> decide

-- ── §0.6 Verb class effect: subject case region ──

/-- Whether the subject maps to the NOM/ERG case region. When true,
    the verbal semantics alone provides maximal contrast between
    subject (NOM/ERG) and object (ACC/ABS or below), and DOM can
    regularize — it is redundant for disambiguation.

    [von-heusinger-2008]: *matar* 'kill' (Class 1, subject →
    NOM/ERG) regularized DOM centuries before *ver* 'see' (Class 2,
    subject → oblique). -/
def SubjectInAgentRegion (subjProfile : EntailmentProfile) : Prop :=
  (GrimmNode.fromSubjectProfile subjProfile).toCaseRegion = .nomErg

instance (p : EntailmentProfile) : Decidable (SubjectInAgentRegion p) := by
  unfold SubjectInAgentRegion; infer_instance

/-- Kick subject → NOM/ERG: maximal verbal contrast.
    Corresponds to *matar* 'kill' — DOM regularized early. -/
theorem kick_subject_in_agent_region :
    SubjectInAgentRegion kickSubjectProfile := by decide

/-- See subject → NOT NOM/ERG: insufficient verbal contrast.
    Corresponds to *ver* 'see' — DOM remained variable. -/
theorem see_subject_not_in_agent_region :
    ¬ SubjectInAgentRegion seeSubjectProfile := by decide

/-- Build subject → NOM/ERG: high verbal contrast, but moot because
    the object is outside the transitivity region (§0.5). -/
theorem build_subject_in_agent_region :
    SubjectInAgentRegion buildSubjectProfile := by decide

-- ── §0.7 Monotonicity: Aissen's staircase from lattice structure ──

/-- The lattice reproduces [aissen-2003]'s monotonicity prediction:
    if DOM is predicted for a lower animacy level, it is also predicted
    for all higher levels. Universally quantified over persistence.

    This is NOT stipulated — it follows from:
    1. `animacyToAgentivity` is monotone (higher animacy → more features)
    2. `toCaseRegion` maps ⊥ agentivity to accAbs, non-⊥ to dative/oblique
    3. Once agentivity is non-⊥, adding features keeps it non-⊥ -/
theorem dom_monotone_inanimate_animate (p : PersistenceLevel) :
    DomPredictedByLattice .inanimate p →
    DomPredictedByLattice .animate p := by
  cases p <;> decide

theorem dom_monotone_animate_human (p : PersistenceLevel) :
    DomPredictedByLattice .animate p →
    DomPredictedByLattice .human p := by
  cases p <;> decide

-- ── §0.8 Limitation: totalPersistence ──

/-! For totalPersistence objects (perception verbs: see, hear, know),
    `toCaseRegion` maps `⟨⊥, totalPersistence⟩` to oblique, not accAbs,
    because totalPersistence is not in {exPersBeginning, quPersBeginning}.
    This means `DomPredictedByLattice` returns true for ALL animacy levels,
    including inanimate — overpredicting DOM for perception verb objects.

    This reflects a genuine theoretical point: Grimm's system treats
    perception verb objects as non-prototypical patients (they are not
    affected or changed). But it means `DomPredictedByLattice` is most
    informative for verbs in the transitivity region's core: contact
    (quPersBeginning) and resultative effective (exPersBeginning) verbs. -/
theorem totalPersistence_all_outside_accAbs (a : AnimacyLevel) :
    (objectNodeWithAnimacy a .totalPersistence).toCaseRegion ≠ .accAbs := by
  cases a <;> decide

-- ════════════════════════════════════════════════════
-- § 1. DOM Profile Matching ([grimm-2011] §4)
-- ════════════════════════════════════════════════════

/-! The lattice predicts DOM when an object is in the transitivity region
    but its nominal agentivity pushes it outside ACC/ABS. For canonical
    transitives (quPersBeginning), this predicts DOM for {animate, human}
    but not {inanimate}. We check each attested animacy-based DOM language
    against this prediction. -/

/-- Russian DOM marks exactly the animacy levels where the lattice
    predicts DOM for canonical transitives. The lattice and Russian
    agree on every cell of the animacy scale.

    Russian: animate + human marked, inanimate unmarked.
    Lattice: animate + human shift to dative region (outside ACC/ABS),
    inanimate stays in ACC/ABS. Exact match. -/
theorem russian_matches_lattice :
    AnimacyLevel.all.all (λ a =>
      russianDOM.marks a .definite ==
      decide (DomPredictedByLattice a .quPersBeginning)) = true := by decide

/-- Spanish DOM is a proper subset of the lattice's prediction.
    Both agree on inanimate (no DOM) and human (DOM), but diverge
    on animate: the lattice predicts DOM (sentience alone shifts to
    dative), but Spanish does not mark animate objects. -/
theorem spanish_subset_of_lattice :
    -- Agreement on inanimate and human
    spanishDOM.marks .inanimate .definite = decide (DomPredictedByLattice .inanimate .quPersBeginning) ∧
    spanishDOM.marks .human .definite = decide (DomPredictedByLattice .human .quPersBeginning) ∧
    -- Divergence on animate
    spanishDOM.marks .animate .definite = false ∧
    DomPredictedByLattice .animate .quPersBeginning :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- Hindi DOM is consistent with the lattice on the animacy dimension:
    inanimate objects are never marked regardless of definiteness, and
    both animate and human are marked at some definiteness level.
    The lattice correctly predicts the animacy boundary even though it
    has no definiteness dimension. -/
theorem hindi_consistent_on_animacy :
    -- Inanimate: never marked (all definiteness levels)
    DefinitenessLevel.all.all (λ d =>
      hindiDOM.marks .inanimate d == false) = true ∧
    -- Animate: marked at some definiteness level
    DefinitenessLevel.all.any (λ d => hindiDOM.marks .animate d) = true ∧
    -- Human: marked at some definiteness level
    DefinitenessLevel.all.any (λ d => hindiDOM.marks .human d) = true :=
  ⟨by native_decide, by native_decide, by native_decide⟩

/-- Every animacy-based DOM language in the sample marks only animacy
    levels where the lattice predicts DOM. The lattice's prediction is
    a superset of every attested animacy-based pattern. -/
theorem animacy_dom_within_lattice :
    [spanishDOM, russianDOM].all (λ dom =>
      AnimacyLevel.all.all (λ a =>
        if dom.marks a .definite
        then decide (DomPredictedByLattice a .quPersBeginning)
        else true)) = true := by decide

-- ════════════════════════════════════════════════════
-- § 2. Cross-Framework Monotonicity (Lattice ↔ [aissen-2003])
-- ════════════════════════════════════════════════════

/-! [aissen-2003] derives DOM monotonicity from OT constraint
    interaction (harmonic alignment of iconicity and economy constraints).
    [grimm-2011] derives it from lattice geometry (animacy maps
    monotonically to agentivity, and `toCaseRegion` preserves the boundary).
    Two independent frameworks, same prediction. -/

/-- A DOM profile derived from the lattice's predictions at a fixed
    persistence level. Since `DomPredictedByLattice` is monotone in
    animacy (§21.7 of AgentivityLattice.lean), this profile is
    automatically an upper set on the animacy scale. -/
def latticeDOM (p : PersistenceLevel) : DOMProfile :=
  { name := "Lattice-derived"
    role := .P
    channel := .flagging
    marks := λ a _ => decide (DomPredictedByLattice a p) }

/-- Every lattice-derived DOM profile is monotone in
    [aissen-2003]'s sense (upper set in the bidimensional grid).
    Universally quantified over all 5 persistence levels.

    This connects the lattice's geometric structure to OT's constraint-based
    monotonicity prediction. The proof goes through because:
    1. `animacyToAgentivity` is monotone (higher animacy → more features)
    2. `toCaseRegion` maps ⊥ agentivity to accAbs, non-⊥ elsewhere
    3. Once non-⊥, the object stays non-⊥ at higher animacy levels -/
theorem lattice_dom_always_monotone (p : PersistenceLevel) :
    (latticeDOM p).isMonotone = true := by
  cases p <;> decide

/-- The lattice's canonical transitive prediction matches
    [aissen-2003]'s OT Type 2 (Hu + An, not In). Two independent
    theories converge on the Russian pattern. -/
theorem lattice_matches_aissen_type2 :
    DomPredictedByLattice .human .quPersBeginning ∧
    DomPredictedByLattice .animate .quPersBeginning ∧
    ¬ DomPredictedByLattice .inanimate .quPersBeginning :=
  ⟨by decide, by decide, by decide⟩

-- ════════════════════════════════════════════════════
-- § 3. Case Regions for Canonical Verbs
-- ════════════════════════════════════════════════════

/-! Every canonical verb with an `EntailmentProfile` is mapped through
    the lattice to a case region. This connects [dowty-1991]'s
    entailment profiles to [grimm-2011]'s case theory:

    | Verb | Subject region | Object region |
    |------|---------------|--------------|
    | kick | nomErg | accAbs |
    | build | nomErg | oblique (creation) |
    | eat | nomErg | accAbs |
    | see | oblique | — |
    | buy/sell | nomErg | — |
    | run | oblique | — |
    | arrive | oblique | — |
    | die | — | accAbs (unacc. subj) |

    The table shows that only verbs whose subjects have instigation
    land in the NOM/ERG region. Perception and motion verbs without
    instigation fall outside — the lattice predicts they are NOT
    prototypical transitive subjects.

    Objects land in ACC/ABS only when they have ⊥ agentivity and
    exist-at-beginning persistence. Creation verbs (exPersEnd) map
    to oblique because the object does not exist at the event's start. -/

-- Transitive verbs

/-- kick: prototypical transitive. Subject → NOM/ERG, object → ACC/ABS. -/
theorem kick_case_regions :
    (GrimmNode.fromSubjectProfile kickSubjectProfile).toCaseRegion = .nomErg ∧
    (GrimmNode.fromObjectProfile kickObjectProfile).toCaseRegion = .accAbs :=
  ⟨by native_decide, by native_decide⟩

/-- build: creation verb. Subject → NOM/ERG (has instigation), but
    object → oblique (exPersEnd: object created, not an existing patient).
    The lattice correctly identifies creation verb objects as
    non-prototypical patients. -/
theorem build_case_regions :
    (GrimmNode.fromSubjectProfile buildSubjectProfile).toCaseRegion = .nomErg ∧
    (GrimmNode.fromObjectProfile buildObjectProfile).toCaseRegion = .oblique :=
  ⟨by native_decide, by native_decide⟩

/-- eat: consumption verb. Subject → NOM/ERG, object → ACC/ABS.
    The consumed object has exPersBeginning (exists before, ceases to
    exist after) — in the same region as destroyed objects. -/
theorem eat_case_regions :
    (GrimmNode.fromSubjectProfile eatSubjectProfile).toCaseRegion = .nomErg ∧
    (GrimmNode.fromObjectProfile eatObjectProfile).toCaseRegion = .accAbs :=
  ⟨by native_decide, by native_decide⟩

-- Intransitive verbs

/-- run: unergative. Has volition + sentience + motion but NOT instigation →
    outside NOM/ERG. The lattice predicts the subject is not a prototypical
    agent — consistent with it being unergative in split-S systems. -/
theorem run_case_region :
    (GrimmNode.fromSubjectProfile runSubjectProfile).toCaseRegion = .oblique := by
  native_decide

/-- see: experiencer verb. Subject has sentience but not instigation →
    outside NOM/ERG. Consistent with many languages giving experiencer
    subjects dative or oblique case (e.g., German *mir gefällt*, Icelandic
    *mér líkar*). -/
theorem see_case_region :
    (GrimmNode.fromSubjectProfile seeSubjectProfile).toCaseRegion = .oblique := by
  native_decide

-- Alternating verbs

/-- buy/sell: both subjects → NOM/ERG (both have instigation via causation).
    The lattice predicts both are prototypical agents — consistent with
    [dowty-1991]'s prediction that buy/sell allow alternation. -/
theorem buy_sell_case_regions :
    (GrimmNode.fromSubjectProfile buySubjectProfile).toCaseRegion = .nomErg ∧
    (GrimmNode.fromSubjectProfile sellSubjectProfile).toCaseRegion = .nomErg :=
  ⟨by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 4. Verb Persistence and Transitivity
-- ════════════════════════════════════════════════════

/-! [grimm-2011]'s Tsunoda hierarchy distinguishes verbs by the
    persistence of their object. This connects [dowty-1991]'s
    P-Patient entailments to [grimm-2011]'s persistence levels:

    | Verb | P-Patient features | Persistence | Tsunoda class |
    |------|-------------------|-------------|--------------|
    | kick | CoS+CA+St | quPersBeginning | contact (II) |
    | eat | CoS+IT+CA | exPersBeginning | result. eff. (I) |
    | build | CoS+IT+CA+DE | exPersEnd | creation (outside) |
    | die | CoS+CA+DE | exPersBeginning | result. eff. (I) |
-/

/-- kick object → quPersBeginning: affected but persists (contact). -/
theorem kick_object_persistence :
    PersistenceLevel.fromPatientProfile kickObjectProfile = .quPersBeginning := by
  native_decide

/-- eat object → exPersBeginning: consumed (ceases to exist via SINC). -/
theorem eat_object_persistence :
    PersistenceLevel.fromPatientProfile eatObjectProfile = .exPersBeginning := by
  native_decide

/-- build object → exPersEnd: created (comes into existence). -/
theorem build_object_persistence :
    PersistenceLevel.fromPatientProfile buildObjectProfile = .exPersEnd := by
  native_decide

/-- die subject → exPersBeginning: ceases to exist (as patient). -/
theorem die_subject_persistence :
    PersistenceLevel.fromPatientProfile dieSubjectProfile = .exPersBeginning := by
  native_decide

/-- kick and eat objects are in the transitivity region; build is not.
    This is the lattice's version of Tsunoda's observation that contact
    and resultative verbs form the core of transitivity. -/
theorem transitivity_membership :
    (GrimmNode.fromObjectProfile kickObjectProfile).InTransitiveRegion ∧
    (GrimmNode.fromObjectProfile eatObjectProfile).InTransitiveRegion ∧
    ¬ (GrimmNode.fromObjectProfile buildObjectProfile).InTransitiveRegion :=
  ⟨by decide, by decide, by decide⟩

-- ════════════════════════════════════════════════════
-- § 5. Verb Class Effect on DOM ([von-heusinger-2008])
-- ════════════════════════════════════════════════════

/-! [von-heusinger-2008] observes that DOM regularized diachronically
    in Spanish at different rates depending on verb class:

    - *matar* 'kill' (Class 1, agent-patient): DOM regularized first
    - *ver* 'see' (Class 2, experiencer-theme): DOM regularized later
    - *poner* 'put' (Class 3, agent-theme-location): DOM intermediate

    The lattice connects this to subject case regions: when the subject
    maps to NOM/ERG, there is maximal semantic contrast between subject
    (prototypical agent) and object (prototypical patient). This contrast
    makes DOM redundant for role identification — so it can regularize.
    When the subject is NOT in NOM/ERG, there is less contrast and DOM
    remains variable. -/

/-- The lattice predicts three verb categories for DOM behavior:
    1. Agent-patient verbs (kick): subject → NOM/ERG, object → ACC/ABS.
       Maximal contrast → DOM can regularize.
    2. Experiencer verbs (see): subject → oblique, outside NOM/ERG.
       Less contrast → DOM remains sensitive to object animacy.
    3. Creation verbs (build): object outside transitivity entirely.
       DOM is structurally inapplicable, not merely unnecessary. -/
theorem verb_class_dom_behavior :
    -- Class 1: both arguments in core case regions
    (GrimmNode.fromSubjectProfile kickSubjectProfile).toCaseRegion = .nomErg ∧
    (GrimmNode.fromObjectProfile kickObjectProfile).toCaseRegion = .accAbs ∧
    -- Class 2: subject NOT in core agent region
    (GrimmNode.fromSubjectProfile seeSubjectProfile).toCaseRegion ≠ .nomErg ∧
    -- Creation: object outside transitivity region entirely
    ¬ (GrimmNode.fromObjectProfile buildObjectProfile).InTransitiveRegion :=
  ⟨by decide, by decide, by decide, by decide⟩

/-- Creation verb objects are outside the transitivity region at ALL
    animacy levels. DOM is structurally inapplicable — the lattice
    predicts no language should have DOM for creation verb objects.

    This is a stronger prediction than "no DOM": even animate/human
    creation objects (build a team, invent a character) should not
    trigger DOM, because the object does not exist at event start. -/
theorem creation_dom_inapplicable (a : AnimacyLevel) :
    ¬ DomPredictedByLattice a .exPersEnd := by
  cases a <;> decide

-- ════════════════════════════════════════════════════
-- § 6. Accusative and Ergative Alignment
-- ════════════════════════════════════════════════════

/-! The lattice-to-case-region mapping predicts morphological case in
    both accusative and ergative systems. For prototypical transitives
    (kick, eat), both alignments produce the expected case assignments. -/

/-- kick in an accusative system: subject → NOM, object → ACC. -/
theorem kick_accusative :
    (GrimmNode.fromSubjectProfile kickSubjectProfile).toCaseRegion.toAccusativeCase = .nom ∧
    (GrimmNode.fromObjectProfile kickObjectProfile).toCaseRegion.toAccusativeCase = .acc :=
  ⟨by native_decide, by native_decide⟩

/-- kick in an ergative system: subject → ERG, object → ABS. -/
theorem kick_ergative :
    (GrimmNode.fromSubjectProfile kickSubjectProfile).toCaseRegion.toErgativeCase = .erg ∧
    (GrimmNode.fromObjectProfile kickObjectProfile).toCaseRegion.toErgativeCase = .abs :=
  ⟨by native_decide, by native_decide⟩

/-- eat in an accusative system: subject → NOM, object → ACC.
    Consumption verbs pattern with canonical transitives for case. -/
theorem eat_accusative :
    (GrimmNode.fromSubjectProfile eatSubjectProfile).toCaseRegion.toAccusativeCase = .nom ∧
    (GrimmNode.fromObjectProfile eatObjectProfile).toCaseRegion.toAccusativeCase = .acc :=
  ⟨by native_decide, by native_decide⟩

/-- build in an accusative system: subject → NOM, but object → INST
    (oblique). The lattice predicts creation verb objects are NOT
    canonical accusatives — consistent with Finnish partitive for
    incomplete creation and Russian genitive of negation being more
    readily available with creation verbs. -/
theorem build_accusative :
    (GrimmNode.fromSubjectProfile buildSubjectProfile).toCaseRegion.toAccusativeCase = .nom ∧
    (GrimmNode.fromObjectProfile buildObjectProfile).toCaseRegion.toAccusativeCase = .inst :=
  ⟨by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 7. NOM/ERG Requires Instigation
-- ════════════════════════════════════════════════════

/-! The lattice's `toCaseRegion` requires instigation for NOM/ERG.
    This captures a cross-linguistic generalization: canonical
    transitive subjects are instigators. Verbs whose subjects lack
    instigation (see, run, arrive) have "oblique" semantics even
    when they surface with NOM in accusative languages. -/

/-- Summary: which verbs have subjects in NOM/ERG and which do not.
    The dividing line is instigation (Dowty's causation). -/
theorem instigation_divides :
    -- With instigation → NOM/ERG
    (GrimmNode.fromSubjectProfile kickSubjectProfile).toCaseRegion = .nomErg ∧
    (GrimmNode.fromSubjectProfile buildSubjectProfile).toCaseRegion = .nomErg ∧
    (GrimmNode.fromSubjectProfile eatSubjectProfile).toCaseRegion = .nomErg ∧
    (GrimmNode.fromSubjectProfile buySubjectProfile).toCaseRegion = .nomErg ∧
    -- Without instigation → oblique
    (GrimmNode.fromSubjectProfile seeSubjectProfile).toCaseRegion = .oblique ∧
    (GrimmNode.fromSubjectProfile runSubjectProfile).toCaseRegion = .oblique ∧
    (GrimmNode.fromSubjectProfile arriveSubjectProfile).toCaseRegion = .oblique :=
  ⟨by native_decide, by native_decide, by native_decide, by native_decide,
   by native_decide, by native_decide, by native_decide⟩

/-- The dividing feature is exactly instigation. All NOM/ERG subjects
    have instigation; all non-NOM/ERG subjects lack it.
    Instigation = Dowty's causation mapped to Grimm's system. -/
theorem instigation_is_the_feature :
    -- NOM/ERG subjects have instigation
    kickSubjectProfile.causation = true ∧
    buildSubjectProfile.causation = true ∧
    eatSubjectProfile.causation = true ∧
    buySubjectProfile.causation = true ∧
    -- Non-NOM/ERG subjects lack instigation
    seeSubjectProfile.causation = false ∧
    runSubjectProfile.causation = false ∧
    arriveSubjectProfile.causation = false :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 8. Russian Genitive/Accusative Alternation ([grimm-2011] §5.2)
-- ════════════════════════════════════════════════════

/-- The Russian genitive/accusative alternation arises when the object
    of an intensional verb (want, seek, await) falls in a region covered
    by two cases. The accusative covers existential persistence (beginning);
    the genitive covers total non-persistence (Fig. 8).

    - Accusative (specific reading): the object is referential → exists
      → existential persistence (beginning) → ACC region.
    - Genitive (non-specific reading): the object need not exist →
      total non-persistence → GEN region.

    The alternation is limited to verbs whose objects have no persistence
    entailments — only intensional verbs like *want*, *seek*, *await*
    license the genitive (p.541). -/
structure GenAccAlternation where
  /-- The object node under the specific/referential reading. -/
  specificReading : GrimmNode
  /-- The object node under the non-specific reading. -/
  nonSpecificReading : GrimmNode
  /-- The specific reading has more persistence features. -/
  specific_more_persistent :
    nonSpecificReading.persistence ≤ specificReading.persistence

/-- The canonical Russian gen/acc alternation for intensional verbs:
    ACC (specific) ↔ GEN (non-specific). -/
def russianGenAcc : GenAccAlternation :=
  { specificReading := ⟨⊥, .exPersBeginning⟩
    nonSpecificReading := ⟨⊥, .totalNonPersistence⟩
    specific_more_persistent := bot_le }

/-- The specific reading maps to the ACC/ABS region. -/
theorem genAcc_specific_is_acc :
    russianGenAcc.specificReading.toCaseRegion = .accAbs := by decide

-- ════════════════════════════════════════════════════
-- § 9. Semantic Opposition ([grimm-2011] §3, p.530)
-- ════════════════════════════════════════════════════

/-- Semantic opposition between two GrimmNodes. Transitivity increases
    with the distance between agent and patient on the lattice. We measure
    this as the difference in total feature counts — higher opposition
    means more prototypically transitive. -/
def semanticOpposition (agent patient : GrimmNode) : Int :=
  (agent.featureCount : Int) - (patient.featureCount : Int)

/-- Maximal agent vs maximal patient has the highest opposition (8 - 2 = 6). -/
theorem maximal_opposition :
    semanticOpposition maximalAgent maximalPatient = 6 := by decide

/-- Class I (break) has more opposition than Class II (shoot):
    the patient is more affected (fewer persistence features). -/
theorem classI_more_opposition_than_classII :
    semanticOpposition effectorAgent
      (TransitivityClass.resultativeEffective.patientNode) >
    semanticOpposition effectorAgent
      (TransitivityClass.contact.patientNode) := by decide

-- ════════════════════════════════════════════════════
-- § 10. Canonical Verb-Agentivity Chain ([grimm-2011] §2.2, p.523–524)
-- ════════════════════════════════════════════════════

/-! Illustrates the agentivity lattice with a chain of canonical verbs,
    each adding one feature. Demonstrates that the lattice directly
    formalises "degree of agentivity" — higher on the lattice means
    more agentive. -/

/-- sit/stand subject: ⊥ (no agentivity). p.523. -/
def sitAgentivity : AgentivityNode := ⊥

/-- know/see subject: sentience only. p.524. -/
def knowAgentivity : AgentivityNode := ⟨false, true, false, false⟩

/-- discover subject: sentience + instigation. p.524. -/
def discoverAgentivity : AgentivityNode := ⟨false, true, true, false⟩

/-- look at subject: sentience + instigation + motion. p.524. -/
def lookAtAgentivity : AgentivityNode := ⟨false, true, true, true⟩

/-- assassinate subject: all four features. p.524. -/
def assassinateAgentivity : AgentivityNode := ⊤

/-- The canonical verb chain is totally ordered and forms a maximal
    chain from ⊥ to ⊤ in the agentivity lattice. -/
theorem canonical_verb_chain :
    sitAgentivity < knowAgentivity ∧
    knowAgentivity < discoverAgentivity ∧
    discoverAgentivity < lookAtAgentivity ∧
    lookAtAgentivity < assassinateAgentivity := by
  refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> decide

/-- All canonical verb positions satisfy volition → sentience. -/
theorem canonical_verbs_valid :
    sitAgentivity.Valid ∧ knowAgentivity.Valid ∧
    discoverAgentivity.Valid ∧ lookAtAgentivity.Valid ∧
    assassinateAgentivity.Valid :=
  ⟨by decide, by decide, by decide, by decide, by decide⟩

-- ════════════════════════════════════════════════════
-- § 11. Projection Kernel Theorems
-- ════════════════════════════════════════════════════

/-- **AgentivityNode kernel**: two profiles map to the same agentivity node
    iff they agree on {V, S, C, M}. The 5th P-Agent feature (IE) and all
    5 P-Patient features are irrelevant — they are dropped by the projection.

    This formally characterizes the information loss: `fromEntailmentProfile`
    is a surjection whose fibers are the equivalence classes of profiles
    agreeing on {V, S, C, M}. -/
theorem fromEntailmentProfile_eq_iff (p q : EntailmentProfile) :
    AgentivityNode.fromEntailmentProfile p =
    AgentivityNode.fromEntailmentProfile q ↔
    p.volition = q.volition ∧ p.sentience = q.sentience ∧
    p.causation = q.causation ∧ p.movement = q.movement := by
  simp [AgentivityNode.fromEntailmentProfile, AgentivityNode.mk.injEq]

/-- Independent existence is lost by the agentivity projection.
    Two profiles differing only in IE map to the same node.
    Concrete witness: full agent (IE=true) and agent-without-IE. -/
theorem fromEntailmentProfile_drops_IE :
    AgentivityNode.fromEntailmentProfile
      ⟨true, true, true, true, true, false, false, false, false, false⟩ =
    AgentivityNode.fromEntailmentProfile
      ⟨true, true, true, true, false, false, false, false, false, false⟩ := rfl

/-- All P-Patient features are lost by the agentivity projection.
    A profile with 5 P-Patient features maps to the same node as one with 0. -/
theorem fromEntailmentProfile_drops_patient :
    AgentivityNode.fromEntailmentProfile
      ⟨true, true, true, true, true, true, true, true, true, true⟩ =
    AgentivityNode.fromEntailmentProfile
      ⟨true, true, true, true, true, false, false, false, false, false⟩ := rfl

-- ════════════════════════════════════════════════════
-- § 12. wellFormedPair Non-Preservation (Grimm vs Dowty)
-- ════════════════════════════════════════════════════

/-- **wellFormedPair is not preserved by the Grimm projection.**

    [dowty-1991]'s `wellFormedPair` constrains inter-argument entailment
    pairings: causation→CoS, movement→stationary, IE→DE. These are
    *relational* constraints between two profiles.

    Grimm's system replaces them with a single persistence dimension on the
    patient side. The IE feature is dropped entirely from the agentivity
    projection, so the IE→DE constraint becomes invisible.

    Witness: s₁ = {C} and s₂ = {C, IE} map to the same AgentivityNode
    (both have instigation only). With o = {CoS}, wellFormedPair holds
    for s₁ (IE=false, so IE→DE vacuously satisfied) but fails for s₂
    (IE=true but DE=false). The Grimm system cannot detect this. -/
theorem wellFormedPair_not_preserved_by_grimm :
    ∃ s₁ o₁ s₂ o₂ : EntailmentProfile,
    WellFormedPair s₁ o₁ ∧ ¬ WellFormedPair s₂ o₂ ∧
    GrimmNode.fromSubjectProfile s₁ = GrimmNode.fromSubjectProfile s₂ ∧
    GrimmNode.fromObjectProfile o₁ = GrimmNode.fromObjectProfile o₂ :=
  ⟨⟨false, false, true, false, false, false, false, false, false, false⟩,
   ⟨false, false, false, false, false, true, false, false, false, false⟩,
   ⟨false, false, true, false, true, false, false, false, false, false⟩,
   ⟨false, false, false, false, false, true, false, false, false, false⟩,
   by decide, by decide, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 13. Tsunoda Hierarchy Membership ([grimm-2011] §3)
-- ════════════════════════════════════════════════════

/-- Class I patients (break) are in the transitivity region. -/
theorem classI_patient_in_region :
    (TransitivityClass.resultativeEffective.patientNode).InTransitiveRegion :=
  by decide

/-- Class II patients (shoot) are in the transitivity region. -/
theorem classII_patient_in_region :
    (TransitivityClass.contact.patientNode).InTransitiveRegion :=
  by decide

/-- Class III patients (search) are OUTSIDE the transitivity region.
    This captures Tsunoda's observation that pursuit verbs deviate most
    strongly from the prototypical transitive paradigm. -/
theorem classIII_patient_outside_region :
    ¬ (TransitivityClass.pursuit.patientNode).InTransitiveRegion :=
  by decide

/-- Class I patient (break: exPersBeginning) has lower persistence than
    Class II patient (shoot: quPersBeginning). The Class I object is
    more affected — it ceases to exist. -/
theorem classI_patient_lower_persistence :
    (TransitivityClass.resultativeEffective.patientNode).persistence.featureCount <
    (TransitivityClass.contact.patientNode).persistence.featureCount := by
  decide

/-- Class I patient ≤ Class II patient on the lattice
    (exPersBeginning ≤ quPersBeginning). -/
theorem classI_patient_le_classII :
    TransitivityClass.resultativeEffective.patientNode ≤
    TransitivityClass.contact.patientNode := by decide

/-- Class III patient ≤ Class I patient
    (totalNonPersistence ≤ exPersBeginning). -/
theorem classIII_patient_le_classI :
    TransitivityClass.pursuit.patientNode ≤
    TransitivityClass.resultativeEffective.patientNode := by decide

-- ════════════════════════════════════════════════════
-- § 14. Named Participants & Alignment ([grimm-2011] §4)
-- ════════════════════════════════════════════════════

/-- Maximal agent maps to NOM/ERG region. -/
theorem maximalAgent_nomErg :
    maximalAgent.toCaseRegion = .nomErg := by decide

/-- Maximal patient maps to ACC/ABS region. -/
theorem maximalPatient_accAbs :
    maximalPatient.toCaseRegion = .accAbs := by decide

/-- The effector agent (instigation + motion, total persistence) maps to
    NOM/ERG. This is the agent of break/kill (Fig. 5, Ia). -/
theorem effectorAgent_nomErg :
    effectorAgent.toCaseRegion = .nomErg := by decide

/-- Class I patient (break object: destroyed) maps to ACC/ABS. -/
theorem classI_patient_accAbs :
    (TransitivityClass.resultativeEffective.patientNode).toCaseRegion
    = .accAbs := by decide

/-- Class II patient (shoot object: affected but persists) maps to ACC/ABS. -/
theorem classII_patient_accAbs :
    (TransitivityClass.contact.patientNode).toCaseRegion
    = .accAbs := by decide

/-- Accusative alignment: maximal agent → NOM, maximal patient → ACC. -/
theorem accusative_alignment :
    maximalAgent.toCaseRegion.toAccusativeCase = .nom ∧
    maximalPatient.toCaseRegion.toAccusativeCase = .acc := ⟨rfl, rfl⟩

/-- Ergative alignment: maximal agent → ERG, maximal patient → ABS. -/
theorem ergative_alignment :
    maximalAgent.toCaseRegion.toErgativeCase = .erg ∧
    maximalPatient.toCaseRegion.toErgativeCase = .abs := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 15. Verb-Profile Bridge Verification
-- ════════════════════════════════════════════════════

/-- kick subject → agentivity {V,S,I,M} (full agent). -/
theorem kick_subject_agentivity :
    AgentivityNode.fromEntailmentProfile kickSubjectProfile
    = ⟨true, true, true, true⟩ := rfl

/-- run subject → agentivity {V,S,M} (no instigation). -/
theorem run_subject_agentivity :
    AgentivityNode.fromEntailmentProfile runSubjectProfile
    = ⟨true, true, false, true⟩ := rfl

/-- arrive subject → agentivity {M} (motion only). -/
theorem arrive_subject_agentivity :
    AgentivityNode.fromEntailmentProfile arriveSubjectProfile
    = ⟨false, false, false, true⟩ := rfl

/-- see subject → agentivity {S} (sentience only). -/
theorem see_subject_agentivity :
    AgentivityNode.fromEntailmentProfile seeSubjectProfile
    = ⟨false, true, false, false⟩ := rfl

/-- sweep basic subject → agentivity {M} (motion only, variable agentivity). -/
theorem sweep_basic_agentivity :
    AgentivityNode.fromEntailmentProfile sweepBasicSubjectProfile
    = ⟨false, false, false, true⟩ := rfl

/-- sweep broom subject → agentivity {V,S,I,M} (instrument lexicalization
    adds full agentivity, [rappaport-hovav-levin-2024]). -/
theorem sweep_broom_agentivity :
    AgentivityNode.fromEntailmentProfile sweepBroomSubjectProfile
    = ⟨true, true, true, true⟩ := rfl

/-- Instrument lexicalization strictly increases agentivity on the lattice:
    sweep basic {M} < sweep broom {V,S,I,M}. -/
theorem sweep_lexicalization_increases :
    AgentivityNode.fromEntailmentProfile sweepBasicSubjectProfile <
    AgentivityNode.fromEntailmentProfile sweepBroomSubjectProfile := by
  constructor <;> decide

-- ════════════════════════════════════════════════════
-- § 16. End-to-End Pipelines: EntailmentProfile → Case
-- ════════════════════════════════════════════════════

/-- Full pipeline: kick subject → GrimmNode → NOM/ERG → NOM (accusative). -/
theorem kick_subject_to_nom :
    (GrimmNode.fromSubjectProfile kickSubjectProfile).toCaseRegion.toAccusativeCase
    = .nom := by decide

/-- Full pipeline: kick object → GrimmNode → ACC/ABS → ACC (accusative). -/
theorem kick_object_to_acc :
    (GrimmNode.fromObjectProfile kickObjectProfile).toCaseRegion.toAccusativeCase
    = .acc := by decide

/-- Build subject → NOM (full agent, total persistence). -/
theorem build_subject_to_nom :
    (GrimmNode.fromSubjectProfile buildSubjectProfile).toCaseRegion.toAccusativeCase
    = .nom := by decide

/-- Build object → OBLIQUE (not ACC). The object of *build* maps to
    exPersEnd (entity comes into existence), which falls OUTSIDE the
    transitivity region (p.529–530). Creation verbs are
    non-prototypically transitive — the object does not exist at the
    beginning of the event to "undergo its effects." This is a correct
    prediction: creation verb objects cross-linguistically show atypical
    case marking (e.g., pseudo-cleft asymmetry). -/
theorem build_object_outside_acc :
    (GrimmNode.fromObjectProfile buildObjectProfile).toCaseRegion ≠ .accAbs := by
  decide

/-- Full pipeline: see subject → OBLIQUE (not NOM/ERG).
    The see-subject has sentience but no instigation, so it falls outside
    the NOM/ERG region. Grimm's system predicts non-canonical case for
    perception verb subjects cross-linguistically. -/
theorem see_subject_not_nomErg :
    (GrimmNode.fromSubjectProfile seeSubjectProfile).toCaseRegion ≠ .nomErg := by
  decide

/-- Full pipeline: die subject (unaccusative) → ACC/ABS.
    The sole argument of *die* maps to the patient region (no agentivity,
    exPersBeginning). In an ergative system this → ABS (= intransitive
    subject). -/
theorem die_subject_to_abs :
    (GrimmNode.fromObjectProfile dieSubjectProfile).toCaseRegion.toErgativeCase
    = .abs := by decide

end Grimm2011
