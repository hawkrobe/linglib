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

Subjects populating a maximal chain: positional verbs at ⊥, then know/see
(sentience), discover (+instigation), look at (+motion), assassinate
(+volition, = ⊤). -/

/-- sit/stand subject: ⊥, p.523. -/
def sitAgentivity : AgentivityNode := ⊥

/-- know/see subject: sentience only, p.523–524. -/
def knowAgentivity : AgentivityNode := ⟨false, true, false, false⟩

/-- discover subject: sentience + instigation, p.524. -/
def discoverAgentivity : AgentivityNode := ⟨false, true, true, false⟩

/-- look at subject: sentience + instigation + motion, p.524. -/
def lookAtAgentivity : AgentivityNode := ⟨false, true, true, true⟩

/-- assassinate subject: all four features, p.524. -/
def assassinateAgentivity : AgentivityNode := ⊤

/-- Each verb adds one feature: a strict chain from ⊥ to ⊤. -/
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
Pursuit (search, seek): the lower the patient's persistence, the more
prototypically transitive the verb. Case regions for the patient nodes are
substrate facts (`Agentivity/CaseRegions.lean`). -/

/-- Class I/II patients are in the transitivity region; Class III (pursuit)
    is outside. -/
theorem tsunoda_region_membership :
    (TransitivityRank.resultativeEffective.patientNode).InTransitiveRegion ∧
    (TransitivityRank.contact.patientNode).InTransitiveRegion ∧
    ¬ (TransitivityRank.pursuit.patientNode).InTransitiveRegion := by decide

/-- Patient nodes are ordered III ≤ I ≤ II: lower persistence, more
    affected. -/
theorem tsunoda_patient_chain :
    TransitivityRank.pursuit.patientNode ≤
      TransitivityRank.resultativeEffective.patientNode ∧
    TransitivityRank.resultativeEffective.patientNode ≤
      TransitivityRank.contact.patientNode := by decide

/-! ### Case regions for canonical verb classes (§4)

Levin-class templates mapped through the lattice: instigation puts subjects
in NOM/ERG; ⊥ agentivity plus change-from-the-beginning persistence puts
objects in ACC/ABS. Contact objects use the project-canonical
no-entailed-change profile (`contactObject_persistence`), which exits
ACC/ABS — [grimm-2011]'s own Fig. 5 keeps them inside at `quPersBeginning`. -/

/-- kick: subject → NOM/ERG; object → oblique under the canonical contact
    profile — a flagged mis-prediction (English gives contact objects plain
    ACC) inherited from the Fig. 5 deviation. -/
theorem kick_case_regions :
    (GrimmNode.fromSubjectProfile mannerContact.subjectProfile).toCaseRegion
      = .nomErg ∧
    (GrimmNode.fromObjectProfile contactObject).toCaseRegion = .oblique := by
  decide

/-- kick/eat objects are in the transitivity region; build objects (not
    existing at event start, p.529–530) are not. -/
theorem kick_object_in_region :
    (GrimmNode.fromObjectProfile contactObject).InTransitiveRegion ∧
    (GrimmNode.fromObjectProfile consumptionObject).InTransitiveRegion ∧
    ¬ (GrimmNode.fromObjectProfile creationObject).InTransitiveRegion := by
  decide

/-- build: subject → NOM/ERG; the created object (`exPersEnd`) → oblique. -/
theorem build_case_regions :
    (GrimmNode.fromSubjectProfile creation.subjectProfile).toCaseRegion
      = .nomErg ∧
    (GrimmNode.fromObjectProfile creationObject).toCaseRegion = .oblique := by
  decide

/-- eat: subject → NOM/ERG; the consumed object → ACC/ABS, with destroyed
    objects. -/
theorem eat_case_regions :
    (GrimmNode.fromSubjectProfile consumption.subjectProfile).toCaseRegion
      = .nomErg ∧
    (GrimmNode.fromObjectProfile consumptionObject).toCaseRegion
      = .accAbs := by decide

/-- buy/sell: subject → NOM/ERG. Buyer and seller share one profile — the
    [dowty-1991] §3.2 alternation tie. -/
theorem possessionTransfer_case_region :
    (GrimmNode.fromSubjectProfile possessionTransfer.subjectProfile).toCaseRegion
      = .nomErg := by decide

/-- see: sentience without instigation → oblique. Experiencer *subjects*
    land outside the dative region — `fromSubjectProfile` fixes total
    persistence, the dative region needs `quPersBeginning`. -/
theorem see_case_region :
    (GrimmNode.fromSubjectProfile perception.subjectProfile).toCaseRegion
      = .oblique := by decide

/-- run: volition + sentience + motion without instigation → oblique,
    matching unergative behaviour in split-S systems. -/
theorem run_case_region :
    (GrimmNode.fromSubjectProfile selfMotion.subjectProfile).toCaseRegion
      = .oblique := by decide

/-- arrive: motion only → oblique. -/
theorem arrive_case_region :
    (GrimmNode.fromSubjectProfile directedMotion.subjectProfile).toCaseRegion
      = .oblique := by decide

/-- die: the sole argument, read as patient, → ACC/ABS; ergative readout
    ABS — the unaccusative pattern. -/
theorem die_case_region :
    (GrimmNode.fromObjectProfile disappearance.subjectProfile).toCaseRegion
      = .accAbs ∧
    (GrimmNode.fromObjectProfile disappearance.subjectProfile).toCaseRegion.toErgativeCase
      = .abs := by decide

/-- Instigation (Dowty's causation) exactly divides NOM/ERG subjects from
    oblique ones. -/
theorem instigation_is_the_dividing_feature :
    mannerContact.subjectProfile.causation = true ∧
    creation.subjectProfile.causation = true ∧
    consumption.subjectProfile.causation = true ∧
    possessionTransfer.subjectProfile.causation = true ∧
    perception.subjectProfile.causation = false ∧
    selfMotion.subjectProfile.causation = false ∧
    directedMotion.subjectProfile.causation = false := by decide

/-! ### Accusative and ergative alignment (§4, Fig. 6)

Morphological readout of the substrate region facts
(`maximalAgent_toCaseRegion` etc.) under the two alignments. -/

/-- Accusative alignment: maximal agent → NOM, maximal patient → ACC. -/
theorem accusative_alignment :
    maximalAgent.toCaseRegion.toAccusativeCase = .nom ∧
    maximalPatient.toCaseRegion.toAccusativeCase = .acc := ⟨rfl, rfl⟩

/-- Ergative alignment: maximal agent → ERG, maximal patient → ABS. -/
theorem ergative_alignment :
    maximalAgent.toCaseRegion.toErgativeCase = .erg ∧
    maximalPatient.toCaseRegion.toErgativeCase = .abs := ⟨rfl, rfl⟩

/-- eat in an accusative system: NOM subject, ACC object. -/
theorem eat_alignment :
    (GrimmNode.fromSubjectProfile consumption.subjectProfile).toCaseRegion.toAccusativeCase
      = .nom ∧
    (GrimmNode.fromObjectProfile consumptionObject).toCaseRegion.toAccusativeCase
      = .acc := by decide

/-! ### Differential object marking (§4, p.534; [grimm-2005])

[grimm-2011] p.534: "it is a combination of verbal and nominal properties
which trigger DOM", deferring the referential side to [grimm-2005]. This
section supplies one lattice encoding — a formaliser construction, not the
paper's: animacy contributes a baseline agentive position, the verb the
object's persistence, and DOM is predicted iff the node is in the
transitivity region but outside ACC/ABS. Grimm himself (following
[aissen-2003]) keeps referential prominence on a separate axis. -/

/-- Ceiling agentivity of a referent type: human ↦ {V, S}, animate ↦ {S},
    inanimate ↦ ⊥. Instigation and motion are event-bound, so never
    contributed; denying animates volition keeps the hierarchy strict — a
    modelling choice, not Grimm's. -/
def animacyToAgentivity : AnimacyLevel → AgentivityNode
  | .human     => ⟨true, true, false, false⟩
  | .animate   => ⟨false, true, false, false⟩
  | .inanimate => ⊥

/-- All animacy-derived nodes satisfy volition → sentience. -/
theorem animacyToAgentivity_valid (a : AnimacyLevel) :
    (animacyToAgentivity a).Valid := by cases a <;> decide

/-- Higher animacy → higher agentivity. -/
theorem animacyToAgentivity_monotone : Monotone animacyToAgentivity :=
  fun _ _ h =>
    (by decide : ∀ a b : AnimacyLevel, a ≤ b →
      animacyToAgentivity a ≤ animacyToAgentivity b) _ _ h

/-- Animacy-derived agentivity × the verb's object persistence. -/
def objectNodeWithAnimacy (a : AnimacyLevel) (p : PersistenceLevel) :
    GrimmNode :=
  ⟨animacyToAgentivity a, p⟩

/-- The key non-circular derivation: at `quPersBeginning`, `toCaseRegion` —
    defined for general case theory, not DOM — separates inanimate objects
    (ACC/ABS) from animate/human ones (dative, Fig. 7). -/
theorem object_regions_by_animacy :
    (objectNodeWithAnimacy .inanimate .quPersBeginning).toCaseRegion
      = .accAbs ∧
    (objectNodeWithAnimacy .animate .quPersBeginning).toCaseRegion
      = .dative ∧
    (objectNodeWithAnimacy .human .quPersBeginning).toCaseRegion
      = .dative := by decide

/-- DOM is predicted: the object node is in the transitivity region but
    outside ACC/ABS. -/
def DomPredictedByLattice (a : AnimacyLevel) (p : PersistenceLevel) : Prop :=
  (objectNodeWithAnimacy a p).InTransitiveRegion ∧
  (objectNodeWithAnimacy a p).toCaseRegion ≠ .accAbs

instance (a : AnimacyLevel) (p : PersistenceLevel) :
    Decidable (DomPredictedByLattice a p) := by
  unfold DomPredictedByLattice; infer_instance

/-- DOM for animate/human but not inanimate objects, for both canonical
    (`quPersBeginning`) and resultative (`exPersBeginning`) transitives. -/
theorem dom_by_animacy :
    ¬ DomPredictedByLattice .inanimate .quPersBeginning ∧
    DomPredictedByLattice .animate .quPersBeginning ∧
    DomPredictedByLattice .human .quPersBeginning ∧
    ¬ DomPredictedByLattice .inanimate .exPersBeginning ∧
    DomPredictedByLattice .animate .exPersBeginning ∧
    DomPredictedByLattice .human .exPersBeginning := by decide

/-- Creation objects (`exPersEnd`) are outside the transitivity region at
    every animacy level: DOM is structurally inapplicable. -/
theorem creation_dom_inapplicable (a : AnimacyLevel) :
    ¬ DomPredictedByLattice a .exPersEnd := by revert a; decide

/-- [aissen-2003]'s monotonicity universal, derived: DOM prediction is
    monotone in animacy at every persistence level — from
    `animacyToAgentivity_monotone` and the region geometry, not
    stipulation. -/
theorem domPredicted_monotone (p : PersistenceLevel) :
    ∀ a a' : AnimacyLevel, a ≤ a' →
      DomPredictedByLattice a p → DomPredictedByLattice a' p := by
  revert p; decide

/-! #### Checking attested DOM languages -/

/-- Russian (animate accusative) marks exactly the lattice-predicted
    cells. -/
theorem russian_dom_matches_lattice :
    ∀ a, russianDOM.marks a .definite = true ↔
      DomPredictedByLattice a .quPersBeginning := by decide

/-- Spanish (human `a`) is a proper subset of the lattice prediction: it
    under-marks the predicted animate cell. -/
theorem spanish_dom_within_lattice :
    (∀ a, spanishDOM.marks a .definite = true →
      DomPredictedByLattice a .quPersBeginning) ∧
    spanishDOM.marks .animate .definite = false ∧
    DomPredictedByLattice .animate .quPersBeginning := by decide

/-- Hindi agrees on the animacy boundary: inanimate never marked,
    animate/human marked at some definiteness level. -/
theorem hindi_dom_consistent_on_animacy :
    (∀ d, hindiDOM.marks .inanimate d = false) ∧
    (∃ d, hindiDOM.marks .animate d = true) ∧
    (∃ d, hindiDOM.marks .human d = true) := by decide

/-! #### The lattice-derived profile against [aissen-2003]'s OT typology -/

/-- The lattice's DOM prediction at a fixed persistence level, as a
    [just-2024]-style differential marking profile. -/
def latticeDOM (p : PersistenceLevel) : DOMProfile :=
  { name := "Lattice-derived"
    role := .P
    channel := .flagging
    marks := λ a _ => decide (DomPredictedByLattice a p) }

/-- Lattice-derived profiles satisfy [aissen-2003]'s monotonicity
    universal, structurally via `isMonotoneP_of`. -/
theorem latticeDOM_isMonotone (p : PersistenceLevel) :
    (latticeDOM p).isMonotone = true :=
  (latticeDOM p).isMonotoneP_of fun ha _ hm =>
    decide_eq_true (domPredicted_monotone p _ _ ha (of_decide_eq_true hm))

/-- At `quPersBeginning` the lattice-derived profile coincides with
    [aissen-2003]'s OT Type 2 (Hu + An; `Aissen2003.anim_type_hu_an`) —
    two frameworks, independent premises, same prediction. -/
theorem latticeDOM_matches_aissen_type2 :
    ∀ a d, (latticeDOM .quPersBeginning).marks a d =
      (animCandToDOM ⟨true, true, false⟩).marks a d := by decide

/-! #### Limitation: total-persistence objects

For `totalPersistence` objects, `toCaseRegion` yields oblique even at ⊥
agentivity, so DOM is over-predicted at every animacy level — the predicate
is informative only for the transitivity region's core. -/

/-- DOM over-predicted at every animacy level at total persistence. -/
theorem totalPersistence_dom_overpredicted (a : AnimacyLevel) :
    DomPredictedByLattice a .totalPersistence := by revert a; decide

/-! ### The verb-class effect on DOM (p.534; [von-heusinger-2008])

Grimm cites [von-heusinger-2008]'s finding that Spanish DOM regularized at
different rates for *matar* 'kill', *ver* 'see', *poner* 'put'. This
section operationalizes Grimm's subject–object opposition gauge through
subject regions: NOM/ERG subjects give maximal contrast (DOM redundant,
free to regularize); oblique-region subjects leave DOM discriminating.
(Von Heusinger's own classification keys on object animacy — the other
side of the same opposition.) -/

/-- The subject profile lands in NOM/ERG. -/
def SubjectInAgentRegion (p : EntailmentProfile) : Prop :=
  (GrimmNode.fromSubjectProfile p).toCaseRegion = .nomErg

instance (p : EntailmentProfile) : Decidable (SubjectInAgentRegion p) := by
  unfold SubjectInAgentRegion; infer_instance

/-- Accomplishment (kill-type) verbs: NOM/ERG subject and ACC/ABS object —
    maximal contrast (*matar*). -/
theorem kill_type_maximal_contrast :
    SubjectInAgentRegion accomplishmentSubjectProfile ∧
    (GrimmNode.fromObjectProfile accomplishmentObjectProfile).toCaseRegion
      = .accAbs := by decide

/-- Perception subjects fall outside NOM/ERG — reduced contrast (*ver*). -/
theorem perception_subject_not_in_agent_region :
    ¬ SubjectInAgentRegion perception.subjectProfile := by decide

/-- Creation subjects are in NOM/ERG, but the object is outside the
    transitivity region, so the contrast is moot
    (`creation_dom_inapplicable`). -/
theorem creation_subject_in_agent_region :
    SubjectInAgentRegion creation.subjectProfile := by decide

/-! ### The Russian genitive/accusative alternation (§5.2, Fig. 8)

Objects of intensional verbs (*want*, *seek*, *await*; p.539–541) take
accusative under the specific reading and genitive under the non-specific
one — a case contrast between two lattice nodes. -/

/-- Specific reading: the object exists — `exPersBeginning`. -/
def specificIntensionalObject : GrimmNode := ⟨⊥, .exPersBeginning⟩

/-- Non-specific reading: existence not entailed — total non-persistence. -/
def nonspecificIntensionalObject : GrimmNode := ⟨⊥, .totalNonPersistence⟩

/-- The specific reading sits in the ACC/ABS region. -/
theorem specific_reading_in_accAbs :
    specificIntensionalObject.toCaseRegion = .accAbs := by decide

/-- The non-specific reading is the lattice bottom — Grimm's governed
    genitive at "the lowest node of the lattice" (p.540). -/
theorem nonspecific_reading_at_bottom :
    nonspecificIntensionalObject = ⊥ := rfl

/-! ### Grimm vs [dowty-1991]

§2.1 recasts Dowty's ten entailments as four agentivity features plus
persistence; the projection kernel is
`AgentivityNode.fromEntailmentProfile_eq_iff`. Below: what the recast loses
(Dowty's pairing constraints) and what it fixes (the *arrive* anomaly) —
cross-theory checks absorbed from `Studies/Dowty1991.lean`, since the
comparison belongs to the later paper. -/

/-- Dowty's `WellFormedPair` is invisible to the projection: a {C} and a
    {C, IE} subject project to the same node (IE is dropped,
    `AgentivityNode.fromEntailmentProfile_eq_iff`), yet against a {CoS}
    object only the first satisfies the IE→DE pairing constraint. -/
theorem wellFormedPair_not_preserved :
    WellFormedPair { causation := true } { changeOfState := true } ∧
    ¬ WellFormedPair { causation := true, independentExistence := true }
        { changeOfState := true } ∧
    GrimmNode.fromSubjectProfile { causation := true }
      = GrimmNode.fromSubjectProfile
          { causation := true, independentExistence := true } := by decide

/-- The *arrive* anomaly resolved: Table 1, the priority ASP, and the
    lattice all say unaccusative; only flat counting diverges. -/
theorem arrive_cross_theory :
    Dowty1991.table1 directedMotion.subjectProfile.volition
        directedMotion.subjectProfile.changeOfState = .unaccusative ∧
    PredictsUnaccusative directedMotion.subjectProfile ∧
    Dowty1991.flatPredictsUnaccusative directedMotion.subjectProfile = false ∧
    (GrimmNode.fromSubjectProfile directedMotion.subjectProfile).toCaseRegion
      ≠ .nomErg := by decide

/-- kick: ASP outranking and the lattice's subject region agree — NOM
    subject. -/
theorem kick_asp_grimm_consistent :
    OutranksForSubject mannerContact.subjectProfile contactObject ∧
    (GrimmNode.fromSubjectProfile mannerContact.subjectProfile).toCaseRegion.toAccusativeCase
      = .nom := by decide

/-- die: priority ASP, flat counting, and the lattice agree on
    unaccusativity. -/
theorem die_asp_grimm_consistent :
    PredictsUnaccusative disappearance.subjectProfile ∧
    Dowty1991.flatPredictsUnaccusative disappearance.subjectProfile = true ∧
    (GrimmNode.fromObjectProfile disappearance.subjectProfile).toCaseRegion
      = .accAbs := by decide

/-- kiss: the subject strictly dominates the object on the lattice —
    `Dowty1991.kiss_asymmetry_is_volition` as order. -/
theorem kiss_subject_dominates :
    AgentivityNode.fromEntailmentProfile Dowty1991.kissObjectProfile <
      AgentivityNode.fromEntailmentProfile Dowty1991.kissSubjectProfile := by
  decide

/-- Dowty's count comparison follows from lattice dominance via
    `featureCount_monotone` and `pAgentScore_decomposition`. -/
theorem kiss_flat_count_from_lattice :
    Dowty1991.kissObjectProfile.pAgentScore ≤
      Dowty1991.kissSubjectProfile.pAgentScore := by
  rw [pAgentScore_decomposition, pAgentScore_decomposition]
  exact Nat.add_le_add
    (AgentivityNode.featureCount_monotone kiss_subject_dominates.le) le_rfl

/-! ### Grimm vs dependent case

`Studies/Aissen2003.lean` Part II assigns abstract ACC to every transitive
object, with DOM a realization filter; Grimm assigns the case *category* by
lattice position. On Grimm's line Spanish *a* is dative, not flagged ACC —
the fault line between structural and semantic case. -/

/-- Animate definite object of a canonical transitive: dependent case says
    ACC, the lattice says DAT — different categories, not different
    spell-outs. -/
theorem lattice_diverges_from_dependent_case :
    objectCase .accusative (mkTrans .animate .definite) = some .acc ∧
    (objectNodeWithAnimacy .animate .quPersBeginning).toCaseRegion.toAccusativeCase
      = .dat ∧
    Case.acc ≠ Case.dat :=
  ⟨rfl, by decide, by decide⟩

/-! ### Bridge verification: template subjects on the lattice

Template subjects project to the expected lattice nodes; *see* lands on the
chain's know/see node. (The *sweep* pair lives in
`Studies/RappaportHovavLevin2024.lean`.) -/

/-- kick subject: full agent (⊤). -/
theorem kick_subject_agentivity :
    AgentivityNode.fromEntailmentProfile mannerContact.subjectProfile = ⊤ :=
  rfl

/-- run subject: {V, S, M} — no instigation. -/
theorem run_subject_agentivity :
    AgentivityNode.fromEntailmentProfile selfMotion.subjectProfile
      = ⟨true, true, false, true⟩ := rfl

/-- arrive subject: {M}. -/
theorem arrive_subject_agentivity :
    AgentivityNode.fromEntailmentProfile directedMotion.subjectProfile
      = ⟨false, false, false, true⟩ := rfl

/-- see subject: the chain's know/see node. -/
theorem see_subject_agentivity :
    AgentivityNode.fromEntailmentProfile perception.subjectProfile
      = knowAgentivity := rfl

end Grimm2011
