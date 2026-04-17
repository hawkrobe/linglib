import Linglib.Theories.Semantics.Verb.AgentivityLattice
import Linglib.Theories.Semantics.Verb.EntailmentProfile
import Linglib.Phenomena.Case.Typology

/-!
# @cite{grimm-2011}: Semantics of Case — Lattice Predictions
@cite{grimm-2011} @cite{aissen-2003} @cite{von-heusinger-2008}

Study file connecting @cite{grimm-2011}'s agentivity lattice
(`Theories/Semantics/Events/AgentivityLattice.lean`) to the differential
object marking profiles in `Phenomena/Case/Typology.lean`.

## Key results

1. **Russian DOM matches the lattice exactly**: for canonical transitives
   (quPersBeginning), `domPredictedByLattice` returns true for exactly
   {animate, human} — the same cells Russian marks.

2. **Spanish DOM is a proper subset**: the lattice predicts DOM for
   {animate, human}, but Spanish only marks {human}.

3. **Two frameworks, same predictions**: the lattice-derived DOM is
   always monotone in @cite{aissen-2003}'s sense, and the lattice's
   canonical transitive prediction exactly matches Aissen's OT Type 2.

4. **Full case region table**: every canonical verb is mapped through
   the lattice to a case region, connecting argument selection to
   morphological case.

5. **Verb class effect**: the lattice predicts that creation verb objects
   are entirely outside the transitivity region (DOM inapplicable), while
   contact and consumption verbs have objects in the canonical patient
   region. This connects to @cite{von-heusinger-2008}'s observation that
   DOM regularized earliest for agent-patient verbs.
-/

namespace Grimm2011

open Semantics.Verb.AgentivityLattice
open Semantics.Verb.EntailmentProfile
open Core.Prominence
open Phenomena.Case.Typology

-- ════════════════════════════════════════════════════
-- § 1. DOM Profile Matching (@cite{grimm-2011} §4)
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
      domPredictedByLattice a .quPersBeginning) = true := by native_decide

/-- Spanish DOM is a proper subset of the lattice's prediction.
    Both agree on inanimate (no DOM) and human (DOM), but diverge
    on animate: the lattice predicts DOM (sentience alone shifts to
    dative), but Spanish does not mark animate objects. -/
theorem spanish_subset_of_lattice :
    -- Agreement on inanimate and human
    spanishDOM.marks .inanimate .definite = domPredictedByLattice .inanimate .quPersBeginning ∧
    spanishDOM.marks .human .definite = domPredictedByLattice .human .quPersBeginning ∧
    -- Divergence on animate
    spanishDOM.marks .animate .definite = false ∧
    domPredictedByLattice .animate .quPersBeginning = true :=
  ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

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
        then domPredictedByLattice a .quPersBeginning
        else true)) = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 2. Cross-Framework Monotonicity (Lattice ↔ @cite{aissen-2003})
-- ════════════════════════════════════════════════════

/-! @cite{aissen-2003} derives DOM monotonicity from OT constraint
    interaction (harmonic alignment of iconicity and economy constraints).
    @cite{grimm-2011} derives it from lattice geometry (animacy maps
    monotonically to agentivity, and `toCaseRegion` preserves the boundary).
    Two independent frameworks, same prediction. -/

/-- A DOM profile derived from the lattice's predictions at a fixed
    persistence level. Since `domPredictedByLattice` is monotone in
    animacy (§21.7 of AgentivityLattice.lean), this profile is
    automatically an upper set on the animacy scale. -/
def latticeDOM (p : PersistenceLevel) : DOMProfile :=
  { name := "Lattice-derived"
    role := .P
    channel := .flagging
    marks := λ a _ => domPredictedByLattice a p }

/-- Every lattice-derived DOM profile is monotone in
    @cite{aissen-2003}'s sense (upper set in the bidimensional grid).
    Universally quantified over all 5 persistence levels.

    This connects the lattice's geometric structure to OT's constraint-based
    monotonicity prediction. The proof goes through because:
    1. `animacyToAgentivity` is monotone (higher animacy → more features)
    2. `toCaseRegion` maps ⊥ agentivity to accAbs, non-⊥ elsewhere
    3. Once non-⊥, the object stays non-⊥ at higher animacy levels -/
theorem lattice_dom_always_monotone (p : PersistenceLevel) :
    (latticeDOM p).isMonotone = true := by
  cases p <;> native_decide

/-- The lattice's canonical transitive prediction matches
    @cite{aissen-2003}'s OT Type 2 (Hu + An, not In). Two independent
    theories converge on the Russian pattern. -/
theorem lattice_matches_aissen_type2 :
    domPredictedByLattice .human .quPersBeginning = true ∧
    domPredictedByLattice .animate .quPersBeginning = true ∧
    domPredictedByLattice .inanimate .quPersBeginning = false :=
  ⟨by native_decide, by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 3. Case Regions for Canonical Verbs
-- ════════════════════════════════════════════════════

/-! Every canonical verb with an `EntailmentProfile` is mapped through
    the lattice to a case region. This connects @cite{dowty-1991}'s
    entailment profiles to @cite{grimm-2011}'s case theory:

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
    @cite{dowty-1991}'s prediction that buy/sell allow alternation. -/
theorem buy_sell_case_regions :
    (GrimmNode.fromSubjectProfile buySubjectProfile).toCaseRegion = .nomErg ∧
    (GrimmNode.fromSubjectProfile sellSubjectProfile).toCaseRegion = .nomErg :=
  ⟨by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 4. Verb Persistence and Transitivity
-- ════════════════════════════════════════════════════

/-! @cite{grimm-2011}'s Tsunoda hierarchy distinguishes verbs by the
    persistence of their object. This connects @cite{dowty-1991}'s
    P-Patient entailments to @cite{grimm-2011}'s persistence levels:

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
    (GrimmNode.fromObjectProfile kickObjectProfile).inTransitiveRegion = true ∧
    (GrimmNode.fromObjectProfile eatObjectProfile).inTransitiveRegion = true ∧
    (GrimmNode.fromObjectProfile buildObjectProfile).inTransitiveRegion = false :=
  ⟨by native_decide, by native_decide, by native_decide⟩

-- ════════════════════════════════════════════════════
-- § 5. Verb Class Effect on DOM (@cite{von-heusinger-2008})
-- ════════════════════════════════════════════════════

/-! @cite{von-heusinger-2008} observes that DOM regularized diachronically
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
    (GrimmNode.fromObjectProfile buildObjectProfile).inTransitiveRegion = false :=
  ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

/-- Creation verb objects are outside the transitivity region at ALL
    animacy levels. DOM is structurally inapplicable — the lattice
    predicts no language should have DOM for creation verb objects.

    This is a stronger prediction than "no DOM": even animate/human
    creation objects (build a team, invent a character) should not
    trigger DOM, because the object does not exist at event start. -/
theorem creation_dom_inapplicable (a : AnimacyLevel) :
    domPredictedByLattice a .exPersEnd = false := by
  cases a <;> native_decide

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

end Grimm2011
