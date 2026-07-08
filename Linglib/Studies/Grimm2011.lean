import Linglib.Semantics.ArgumentStructure.Agentivity.CaseRegions
import Linglib.Semantics.ArgumentStructure.EntailmentProfile
import Linglib.Semantics.Lexical.LevinClassProfiles
import Linglib.Studies.Aissen2003
import Linglib.Studies.Dowty1991

/-!
# Semantics of Case ([grimm-2011])

Study file for [grimm-2011]: canonical verbs mapped through the agentivity
lattice (`Semantics/ArgumentStructure/Agentivity/`) to case regions, a
lattice-derived account of differential object marking checked against the
[aissen-2003] DOM profiles, and the paper's engagement with [dowty-1991]'s
Argument Selection Principle. The DOM substrate reconstructs the
referential-property treatment the paper attributes to [grimm-2005].

## Main results

- `russian_dom_matches_lattice` / `spanish_dom_within_lattice`: for canonical
  transitives the lattice predicts DOM for exactly {animate, human} — the
  Russian pattern; Spanish marks a proper subset.
- `domPredicted_monotone`, `latticeDOM_isMonotone`,
  `latticeDOM_matches_aissen_type2`: the lattice derives [aissen-2003]'s
  monotonicity universal and reproduces OT Type 2.
- `wellFormedPair_not_preserved`, `arrive_cross_theory`,
  `kiss_flat_count_from_lattice`: what the lattice projection of
  [dowty-1991]'s profiles loses and what it fixes.
- `lattice_diverges_from_dependent_case`: the semantic-case vs
  structural-case fault line on animate objects, made explicit against the
  dependent-case pipeline in `Studies/Aissen2003.lean`.
-/

namespace Grimm2011

open ArgumentStructure.AgentivityLattice
open ArgumentStructure (EntailmentProfile)
open ArgumentStructure.EntailmentProfile
open Features.LevinClassProfiles
open Features.Prominence
open Aissen2003

/-! ### The canonical verb chain (§2.2, p.523–524)

Grimm illustrates the agentivity lattice with subjects populating a maximal
chain: positional verbs at ⊥, then know/see (sentience), discover
(+instigation), look at (+motion), assassinate (+volition, = ⊤). -/

/-- sit/stand subject: ⊥ (no agentivity entailed), p.523. -/
def sitAgentivity : AgentivityNode := ⊥

/-- know/see subject: sentience only, p.523–524. -/
def knowAgentivity : AgentivityNode := ⟨false, true, false, false⟩

/-- discover subject: sentience + instigation, p.524. -/
def discoverAgentivity : AgentivityNode := ⟨false, true, true, false⟩

/-- look at subject: sentience + instigation + motion, p.524. -/
def lookAtAgentivity : AgentivityNode := ⟨false, true, true, true⟩

/-- assassinate subject: all four features, p.524. -/
def assassinateAgentivity : AgentivityNode := ⊤

/-- The chain is strictly increasing from ⊥ to ⊤: each verb adds one
    feature, so the lattice directly formalises "degree of agentivity". -/
theorem canonical_verb_chain :
    sitAgentivity < knowAgentivity ∧ knowAgentivity < discoverAgentivity ∧
    discoverAgentivity < lookAtAgentivity ∧
    lookAtAgentivity < assassinateAgentivity := by decide

/-- All chain positions satisfy volition → sentience. -/
theorem canonical_verbs_valid :
    sitAgentivity.Valid ∧ knowAgentivity.Valid ∧ discoverAgentivity.Valid ∧
    lookAtAgentivity.Valid ∧ assassinateAgentivity.Valid := by decide

/-! ### Tsunoda's transitivity hierarchy (§3, example 8)

Resultative Effective Action (kill, break) >> Contact (shoot, hit) >>
Pursuit (search, seek). The hierarchy emerges from the patient's position:
the lower its persistence, the further it sits from the agent and the more
prototypically transitive the verb. Case-region placements for the three
patient nodes are substrate facts
(`resultativeEffective_patient_toCaseRegion` etc. in
`Agentivity/CaseRegions.lean`). -/

/-- Class I and II patients are in the transitivity region; Class III
    patients (pursuit: the object may not exist) are outside it. -/
theorem tsunoda_region_membership :
    (TransitivityRank.resultativeEffective.patientNode).InTransitiveRegion ∧
    (TransitivityRank.contact.patientNode).InTransitiveRegion ∧
    ¬ (TransitivityRank.pursuit.patientNode).InTransitiveRegion := by decide

/-- The patient nodes are ordered by persistence: Class III ≤ Class I ≤
    Class II. Lower persistence = more affected = higher transitivity. -/
theorem tsunoda_patient_chain :
    TransitivityRank.pursuit.patientNode ≤
      TransitivityRank.resultativeEffective.patientNode ∧
    TransitivityRank.resultativeEffective.patientNode ≤
      TransitivityRank.contact.patientNode := by decide

/-! ### Case regions for canonical verb classes (§4)

Levin-class templates (`Semantics/Lexical/LevinClassProfiles.lean`) mapped
through the lattice to case regions. Only subjects with instigation land in
NOM/ERG; objects land in ACC/ABS only with ⊥ agentivity and persistence
entailing change from the beginning. Contact objects use the
project-canonical surface-contact profile (no entailed change,
`contactObject_persistence`), which exits the ACC/ABS region — [grimm-2011]'s
own Fig. 5 places them at `quPersBeginning`, inside it. -/

/-- kick (contact, Tsunoda II): subject → NOM/ERG; the object, at total
    persistence under the canonical contact profile, falls outside ACC/ABS
    into the oblique region — though still inside the transitivity region
    (`kick_object_in_region`). English gives contact objects plain
    accusative, so the oblique placement is a flagged mis-prediction
    inherited from the canonical profile's deviation from Fig. 5. -/
theorem kick_case_regions :
    (GrimmNode.fromSubjectProfile mannerContact.subjectProfile).toCaseRegion
      = .nomErg ∧
    (GrimmNode.fromObjectProfile contactObject).toCaseRegion = .oblique := by
  decide

/-- kick and eat objects are in the transitivity region; build objects are
    not — the object of a creation verb does not exist at event start
    (p.529–530), so DOM and core object case are structurally inapplicable. -/
theorem kick_object_in_region :
    (GrimmNode.fromObjectProfile contactObject).InTransitiveRegion ∧
    (GrimmNode.fromObjectProfile consumptionObject).InTransitiveRegion ∧
    ¬ (GrimmNode.fromObjectProfile creationObject).InTransitiveRegion := by
  decide

/-- build (creation): subject → NOM/ERG, object → oblique (`exPersEnd`
    persistence, `creationObject_persistence`). Consistent with atypical
    object case for creation verbs (Finnish partitive for incomplete
    creation, Russian genitive of negation). -/
theorem build_case_regions :
    (GrimmNode.fromSubjectProfile creation.subjectProfile).toCaseRegion
      = .nomErg ∧
    (GrimmNode.fromObjectProfile creationObject).toCaseRegion = .oblique := by
  decide

/-- eat (consumption): subject → NOM/ERG, object → ACC/ABS — the consumed
    object (`consumptionObject_persistence`) patterns with destroyed
    objects, in the core patient region. -/
theorem eat_case_regions :
    (GrimmNode.fromSubjectProfile consumption.subjectProfile).toCaseRegion
      = .nomErg ∧
    (GrimmNode.fromObjectProfile consumptionObject).toCaseRegion
      = .accAbs := by decide

/-- buy/sell (possession transfer): subject → NOM/ERG. Buyer and seller
    share one template profile (`possessionTransfer`), so a single region
    fact covers both — the profile identity is the [dowty-1991] §3.2
    alternation tie. -/
theorem possessionTransfer_case_region :
    (GrimmNode.fromSubjectProfile possessionTransfer.subjectProfile).toCaseRegion
      = .nomErg := by decide

/-- see (perception): sentience without instigation → oblique, outside
    NOM/ERG. Consistent with dative/oblique experiencer subjects (German
    *mir gefällt*, Icelandic *mér líkar*) — though note the lattice routes
    experiencer *subjects* to oblique, not to the dative region proper,
    because `GrimmNode.fromSubjectProfile` fixes total persistence while
    the dative region requires `quPersBeginning`. -/
theorem see_case_region :
    (GrimmNode.fromSubjectProfile perception.subjectProfile).toCaseRegion
      = .oblique := by decide

/-- run (self-motion): volition + sentience + motion but no instigation →
    oblique. The lattice predicts a non-prototypical transitive subject,
    consistent with unergative behaviour in split-S systems. -/
theorem run_case_region :
    (GrimmNode.fromSubjectProfile selfMotion.subjectProfile).toCaseRegion
      = .oblique := by decide

/-- arrive (directed motion): motion only → oblique. -/
theorem arrive_case_region :
    (GrimmNode.fromSubjectProfile directedMotion.subjectProfile).toCaseRegion
      = .oblique := by decide

/-- die (disappearance): the sole argument, read as patient, → ACC/ABS; in
    an ergative system this is ABS — the unaccusative pattern. -/
theorem die_case_region :
    (GrimmNode.fromObjectProfile disappearance.subjectProfile).toCaseRegion
      = .accAbs ∧
    (GrimmNode.fromObjectProfile disappearance.subjectProfile).toCaseRegion.toErgativeCase
      = .abs := by decide

/-- The feature dividing NOM/ERG subjects from oblique ones is exactly
    instigation (Dowty's causation under the [grimm-2011] §2.1 bridge):
    kick/build/eat/buy subjects have it, see/run/arrive subjects lack it. -/
theorem instigation_is_the_dividing_feature :
    mannerContact.subjectProfile.causation = true ∧
    creation.subjectProfile.causation = true ∧
    consumption.subjectProfile.causation = true ∧
    possessionTransfer.subjectProfile.causation = true ∧
    perception.subjectProfile.causation = false ∧
    selfMotion.subjectProfile.causation = false ∧
    directedMotion.subjectProfile.causation = false := by decide

/-! ### Accusative and ergative alignment (§4, Fig. 6)

Region placements for the named participants are substrate facts
(`maximalAgent_toCaseRegion` etc.); the study keeps only the morphological
readout under the two alignments. -/

/-- Accusative alignment: maximal agent → NOM, maximal patient → ACC. -/
theorem accusative_alignment :
    maximalAgent.toCaseRegion.toAccusativeCase = .nom ∧
    maximalPatient.toCaseRegion.toAccusativeCase = .acc := ⟨rfl, rfl⟩

/-- Ergative alignment: maximal agent → ERG, maximal patient → ABS. -/
theorem ergative_alignment :
    maximalAgent.toCaseRegion.toErgativeCase = .erg ∧
    maximalPatient.toCaseRegion.toErgativeCase = .abs := ⟨rfl, rfl⟩

/-- eat under both alignments: NOM/ACC and ERG/ABS — consumption verbs are
    core transitives for case. -/
theorem eat_alignment :
    (GrimmNode.fromSubjectProfile consumption.subjectProfile).toCaseRegion.toAccusativeCase
      = .nom ∧
    (GrimmNode.fromObjectProfile consumptionObject).toCaseRegion.toAccusativeCase
      = .acc := by decide

/-! ### Differential object marking (§4, p.534; [grimm-2005])

[grimm-2011] p.534: "it is a combination of verbal and nominal properties
which trigger DOM." The paper defers the referential-property treatment to
[grimm-2005]; this section supplies one lattice encoding of that
combination — a formaliser construction in the paper's spirit, not a
mechanism stated in it: nominal animacy contributes a baseline agentive
position, the verb contributes the object's persistence, and DOM is
predicted exactly when the resulting node is in the transitivity region but
outside ACC/ABS. Caveat: Grimm (following [aissen-2003]) keeps referential
prominence on an axis separate from the event-entailed agentivity features;
folding animacy onto the agentivity primitives is this file's move. -/

/-- Baseline agentive capacity of a referent type, read as a ceiling: the
    highest agentivity node a referent of that type can occupy. Only
    capacity-like properties are mapped — instigation and motion are
    event-bound: human ↦ {V, S}, animate ↦ {S}, inanimate ↦ ⊥. Denying
    non-human animates volition is a modelling choice (it keeps the animacy
    hierarchy strict on the lattice), not a claim of Grimm's. -/
def animacyToAgentivity : AnimacyLevel → AgentivityNode
  | .human     => ⟨true, true, false, false⟩
  | .animate   => ⟨false, true, false, false⟩
  | .inanimate => ⊥

/-- All animacy-derived nodes satisfy volition → sentience. -/
theorem animacyToAgentivity_valid (a : AnimacyLevel) :
    (animacyToAgentivity a).Valid := by cases a <;> decide

/-- Higher animacy → higher agentivity, as lattice monotonicity. -/
theorem animacyToAgentivity_monotone : Monotone animacyToAgentivity :=
  fun _ _ h =>
    (by decide : ∀ a b : AnimacyLevel, a ≤ b →
      animacyToAgentivity a ≤ animacyToAgentivity b) _ _ h

/-- Object node: the referent's animacy-derived agentivity combined with
    the verb's persistence for the object slot. -/
def objectNodeWithAnimacy (a : AnimacyLevel) (p : PersistenceLevel) :
    GrimmNode :=
  ⟨animacyToAgentivity a, p⟩

/-- **The key non-circular derivation.** For canonical transitive objects
    (`quPersBeginning`, Grimm's Fig. 5 placement for contact objects),
    `toCaseRegion` — defined for general case theory, not for DOM —
    automatically separates inanimate objects (ACC/ABS) from animate and
    human ones (dative region, Fig. 7): sentience alone shifts the node
    out of the core object region. -/
theorem object_regions_by_animacy :
    (objectNodeWithAnimacy .inanimate .quPersBeginning).toCaseRegion
      = .accAbs ∧
    (objectNodeWithAnimacy .animate .quPersBeginning).toCaseRegion
      = .dative ∧
    (objectNodeWithAnimacy .human .quPersBeginning).toCaseRegion
      = .dative := by decide

/-- DOM is predicted when the object is in the transitivity region but its
    nominal agentivity pushes it outside the ACC/ABS region. -/
def DomPredictedByLattice (a : AnimacyLevel) (p : PersistenceLevel) : Prop :=
  (objectNodeWithAnimacy a p).InTransitiveRegion ∧
  (objectNodeWithAnimacy a p).toCaseRegion ≠ .accAbs

instance (a : AnimacyLevel) (p : PersistenceLevel) :
    Decidable (DomPredictedByLattice a p) := by
  unfold DomPredictedByLattice; infer_instance

/-- Canonical transitives: DOM predicted for animate and human objects,
    not inanimate ones. The same split holds for resultative objects
    (`exPersBeginning`). -/
theorem dom_by_animacy :
    ¬ DomPredictedByLattice .inanimate .quPersBeginning ∧
    DomPredictedByLattice .animate .quPersBeginning ∧
    DomPredictedByLattice .human .quPersBeginning ∧
    ¬ DomPredictedByLattice .inanimate .exPersBeginning ∧
    DomPredictedByLattice .animate .exPersBeginning ∧
    DomPredictedByLattice .human .exPersBeginning := by decide

/-- Creation-verb objects (`exPersEnd`) are outside the transitivity region
    at every animacy level: DOM is structurally inapplicable, not merely
    unnecessary — even a human creation object (assemble a team) should not
    trigger DOM. -/
theorem creation_dom_inapplicable (a : AnimacyLevel) :
    ¬ DomPredictedByLattice a .exPersEnd := by revert a; decide

/-- **[aissen-2003]'s monotonicity universal, derived.** DOM prediction is
    monotone in animacy at every persistence level. Not stipulated: it
    follows from `animacyToAgentivity_monotone` and the geometry of
    `toCaseRegion` (⊥ agentivity ↦ ACC/ABS; adding features keeps the node
    outside it). -/
theorem domPredicted_monotone (p : PersistenceLevel) :
    ∀ a a' : AnimacyLevel, a ≤ a' →
      DomPredictedByLattice a p → DomPredictedByLattice a' p := by
  revert p; decide

/-! #### Checking attested DOM languages -/

/-- Russian (animate accusative) marks exactly the animacy levels where the
    lattice predicts DOM for canonical transitives: agreement on every cell
    of the animacy scale. -/
theorem russian_dom_matches_lattice :
    ∀ a, russianDOM.marks a .definite = true ↔
      DomPredictedByLattice a .quPersBeginning := by decide

/-- Spanish (human `a`-marking) is a proper subset of the lattice
    prediction: everything Spanish marks is lattice-predicted, but the
    lattice also predicts DOM for animates, which Spanish leaves unmarked. -/
theorem spanish_dom_within_lattice :
    (∀ a, spanishDOM.marks a .definite = true →
      DomPredictedByLattice a .quPersBeginning) ∧
    spanishDOM.marks .animate .definite = false ∧
    DomPredictedByLattice .animate .quPersBeginning := by decide

/-- Hindi (animacy × definiteness) agrees with the lattice on the animacy
    boundary: inanimate objects are never marked at any definiteness level,
    while animate and human objects are marked at some level. The lattice
    has no definiteness axis, so this is the strongest available check. -/
theorem hindi_dom_consistent_on_animacy :
    (∀ d, hindiDOM.marks .inanimate d = false) ∧
    (∃ d, hindiDOM.marks .animate d = true) ∧
    (∃ d, hindiDOM.marks .human d = true) := by decide

/-! #### The lattice-derived profile against [aissen-2003]'s OT typology -/

/-- The lattice's DOM prediction at a fixed persistence level, packaged as
    a [just-2024]-style differential marking profile for comparison with
    the OT-generated types. -/
def latticeDOM (p : PersistenceLevel) : DOMProfile :=
  { name := "Lattice-derived"
    role := .P
    channel := .flagging
    marks := λ a _ => decide (DomPredictedByLattice a p) }

/-- Every lattice-derived profile satisfies [aissen-2003]'s monotonicity
    universal, structurally: `domPredicted_monotone` discharges the
    pointwise hypothesis of `isMonotoneP_of`. -/
theorem latticeDOM_isMonotone (p : PersistenceLevel) :
    (latticeDOM p).isMonotone = true :=
  (latticeDOM p).isMonotoneP_of fun ha _ hm =>
    decide_eq_true (domPredicted_monotone p _ _ ha (of_decide_eq_true hm))

/-- For canonical transitives the lattice-derived profile coincides with
    [aissen-2003]'s OT Type 2 (mark Hu + An, not In) on every cell — the
    Russian pattern. Type 2 is generated by the OT factorial typology
    (`Aissen2003.anim_type_hu_an`), so the two frameworks converge from
    independent premises: constraint interaction there, lattice geometry
    here. -/
theorem latticeDOM_matches_aissen_type2 :
    ∀ a d, (latticeDOM .quPersBeginning).marks a d =
      (animCandToDOM ⟨true, true, false⟩).marks a d := by decide

/-! #### Limitation: total-persistence objects

For perception-verb objects (`totalPersistence`), `toCaseRegion` yields
oblique even at ⊥ agentivity, so `DomPredictedByLattice` holds at every
animacy level — over-predicting DOM for inanimate perception objects. This
reflects a real feature of the system (perception objects are
non-prototypical patients), but it means the DOM predicate is informative
only for verbs in the transitivity region's core. -/

theorem totalPersistence_dom_overpredicted (a : AnimacyLevel) :
    DomPredictedByLattice a .totalPersistence := by revert a; decide

/-! ### The verb-class effect on DOM (p.534; [von-heusinger-2008])

Grimm cites [von-heusinger-2008]'s corpus finding that Spanish DOM
regularized at different rates for *matar* 'kill', *ver* 'see', and *poner*
'put' as support for verbal properties conditioning DOM. Grimm's own gauge
is the subject–object opposition on the lattice; this section
operationalizes it through subject regions: a NOM/ERG subject gives maximal
semantic contrast with the object, leaving DOM redundant for role
discrimination — free to regularize; an oblique-region subject (perception)
leaves DOM doing discriminatory work, so it stays variable. (Von Heusinger's
own classification keys on the object animacy a verb selects, i.e. the
object side of the same opposition.) -/

/-- The subject maps to the NOM/ERG region: verbal semantics alone provides
    maximal subject–object contrast. -/
def SubjectInAgentRegion (p : EntailmentProfile) : Prop :=
  (GrimmNode.fromSubjectProfile p).toCaseRegion = .nomErg

instance (p : EntailmentProfile) : Decidable (SubjectInAgentRegion p) := by
  unfold SubjectInAgentRegion; infer_instance

/-- kill-type verbs (accomplishment template): subject in NOM/ERG, object
    in ACC/ABS — maximal contrast, DOM free to regularize (*matar*). -/
theorem kill_type_maximal_contrast :
    SubjectInAgentRegion accomplishmentSubjectProfile ∧
    (GrimmNode.fromObjectProfile accomplishmentObjectProfile).toCaseRegion
      = .accAbs := by decide

/-- Perception verbs: subject outside NOM/ERG — reduced contrast, DOM
    stays animacy-sensitive (*ver*). -/
theorem perception_subject_not_in_agent_region :
    ¬ SubjectInAgentRegion perception.subjectProfile := by decide

/-- Creation verbs: subject in NOM/ERG, but the object is outside the
    transitivity region (`kick_object_in_region`), so the contrast question
    is moot — DOM is inapplicable (`creation_dom_inapplicable`). -/
theorem creation_subject_in_agent_region :
    SubjectInAgentRegion creation.subjectProfile := by decide

/-! ### The Russian genitive/accusative alternation (§5.2, Fig. 8)

Objects of intensional verbs (*want*, *seek*, *await*; p.539–541) alternate:
accusative under the specific reading, genitive under the non-specific one.
The two readings occupy different lattice nodes — the alternation is a case
contrast within one predicate's entailment space. -/

/-- The object node under the specific/referential reading: the object
    exists, with no other entailments — `exPersBeginning`. -/
def specificIntensionalObject : GrimmNode := ⟨⊥, .exPersBeginning⟩

/-- The object node under the non-specific reading: existence is not
    entailed — total non-persistence. -/
def nonspecificIntensionalObject : GrimmNode := ⟨⊥, .totalNonPersistence⟩

/-- The specific reading sits in the ACC/ABS region. -/
theorem specific_reading_in_accAbs :
    specificIntensionalObject.toCaseRegion = .accAbs := by decide

/-- The non-specific reading is the lattice bottom — Grimm's placement of
    the governed genitive at "the lowest node of the lattice, total
    non-persistence" (p.540, via the genitive of negation). -/
theorem nonspecific_reading_at_bottom :
    nonspecificIntensionalObject = ⊥ := rfl

/-! ### Grimm vs [dowty-1991]

[grimm-2011] §2.1 recasts Dowty's ten proto-role entailments as four
agentivity features plus a persistence axis. The projection's kernel is
characterized in the substrate
(`AgentivityNode.fromEntailmentProfile_eq_iff`); here we record what the
recast loses (Dowty's inter-argument constraints) and what it fixes (the
*arrive* anomaly), absorbing the cross-theory checks formerly in
`Studies/Dowty1991.lean` §8 — the comparison belongs to the later paper. -/

/-- **Dowty's `WellFormedPair` is invisible to the Grimm projection.** The
    pairing constraints (causation→CoS, movement→stationary, IE→DE) are
    relational; the projection drops IE, so profile pairs on opposite sides
    of the IE→DE constraint can project to identical node pairs. -/
theorem wellFormedPair_not_preserved :
    ∃ s₁ o₁ s₂ o₂ : EntailmentProfile,
      WellFormedPair s₁ o₁ ∧ ¬ WellFormedPair s₂ o₂ ∧
      GrimmNode.fromSubjectProfile s₁ = GrimmNode.fromSubjectProfile s₂ ∧
      GrimmNode.fromObjectProfile o₁ = GrimmNode.fromObjectProfile o₂ :=
  ⟨⟨false, false, true, false, false, false, false, false, false, false⟩,
   ⟨false, false, false, false, false, true, false, false, false, false⟩,
   ⟨false, false, true, false, true, false, false, false, false, false⟩,
   ⟨false, false, false, false, false, true, false, false, false, false⟩,
   by decide, by decide, rfl, rfl⟩

/-- The *arrive* anomaly, resolved: Table 1, the priority-based ASP, and
    the lattice all classify *arrive* as unaccusative/non-agent; only flat
    counting diverges ([dowty-1991]'s own worry). -/
theorem arrive_cross_theory :
    Dowty1991.table1 directedMotion.subjectProfile.volition
        directedMotion.subjectProfile.changeOfState = .unaccusative ∧
    PredictsUnaccusative directedMotion.subjectProfile ∧
    Dowty1991.flatPredictsUnaccusative directedMotion.subjectProfile = false ∧
    (GrimmNode.fromSubjectProfile directedMotion.subjectProfile).toCaseRegion
      ≠ .nomErg := by decide

/-- kick: ASP outranking and the lattice's subject region converge on the
    subject; the object lands outside canonical ACC under the canonical
    contact profile (see `kick_case_regions`). -/
theorem kick_asp_grimm_consistent :
    OutranksForSubject mannerContact.subjectProfile contactObject ∧
    (GrimmNode.fromSubjectProfile mannerContact.subjectProfile).toCaseRegion.toAccusativeCase
      = .nom := by decide

/-- die: priority ASP, flat counting, and the lattice agree on
    unaccusativity — the sole argument sits in the patient region. -/
theorem die_asp_grimm_consistent :
    PredictsUnaccusative disappearance.subjectProfile ∧
    Dowty1991.flatPredictsUnaccusative disappearance.subjectProfile = true ∧
    (GrimmNode.fromObjectProfile disappearance.subjectProfile).toCaseRegion
      = .accAbs := by decide

/-- kiss: the subject strictly dominates the object on the agentivity
    lattice — Dowty's counting asymmetry
    (`Dowty1991.kiss_asymmetry_is_volition`) restated as lattice order. -/
theorem kiss_subject_dominates :
    AgentivityNode.fromEntailmentProfile Dowty1991.kissObjectProfile <
      AgentivityNode.fromEntailmentProfile Dowty1991.kissSubjectProfile := by
  decide

/-- The flat-count comparison follows from lattice dominance via
    `featureCount_monotone` and `pAgentScore_decomposition`: Dowty's
    counting is a consequence of Grimm's order. -/
theorem kiss_flat_count_from_lattice :
    Dowty1991.kissObjectProfile.pAgentScore ≤
      Dowty1991.kissSubjectProfile.pAgentScore := by
  rw [pAgentScore_decomposition, pAgentScore_decomposition]
  exact Nat.add_le_add
    (AgentivityNode.featureCount_monotone kiss_subject_dominates.le) le_rfl

/-! ### Grimm vs dependent case

`Studies/Aissen2003.lean` Part II runs a structural pipeline: dependent
case assigns abstract ACC to every transitive object regardless of
prominence (`Aissen2003.object_always_acc`), and DOM only filters overt
realization. Grimm's semantic case assigns the *category* by lattice
position instead. The two disagree on the animate object of a canonical
transitive — structural ACC vs inherent dative — the fault line between
structural-case-plus-flagging and semantic-case theories of DOM
(Spanish *a* is, on Grimm's line, dative marking, not flagged ACC). -/

/-- On the animate definite object of a canonical transitive, dependent
    case says ACC while the lattice says DAT — the frameworks assign
    different case categories, not just different spell-outs. -/
theorem lattice_diverges_from_dependent_case :
    objectCase .accusative (mkTrans .animate .definite) = some .acc ∧
    (objectNodeWithAnimacy .animate .quPersBeginning).toCaseRegion.toAccusativeCase
      = .dat ∧
    Case.acc ≠ Case.dat :=
  ⟨rfl, by decide, by decide⟩

/-! ### Bridge verification: template subjects on the lattice

The Levin-template subjects project to the expected agentivity nodes; *see*
lands on the canonical chain's know/see node. (The *sweep* pair lives with
its paper in `Studies/RappaportHovavLevin2024.lean`.) -/

/-- kick subject: full agent {V, S, I, M}. -/
theorem kick_subject_agentivity :
    AgentivityNode.fromEntailmentProfile mannerContact.subjectProfile = ⊤ :=
  rfl

/-- run subject: {V, S, M} — no instigation. -/
theorem run_subject_agentivity :
    AgentivityNode.fromEntailmentProfile selfMotion.subjectProfile
      = ⟨true, true, false, true⟩ := rfl

/-- arrive subject: {M} — motion only. -/
theorem arrive_subject_agentivity :
    AgentivityNode.fromEntailmentProfile directedMotion.subjectProfile
      = ⟨false, false, false, true⟩ := rfl

/-- see subject: {S} — exactly the canonical chain's know/see node. -/
theorem see_subject_agentivity :
    AgentivityNode.fromEntailmentProfile perception.subjectProfile
      = knowAgentivity := rfl

end Grimm2011
