import Linglib.Semantics.ArgumentStructure.CaseRegion
import Linglib.Semantics.ArgumentStructure.Projection
import Linglib.Semantics.ArgumentStructure.LevinClassProfiles
import Linglib.Studies.Aissen2003
import Linglib.Studies.Dowty1991

/-!
# Semantics of Case ([grimm-2011])

Study file for [grimm-2011]: canonical verbs mapped through the agentivity
lattice (`Semantics/ArgumentStructure/`) to case regions, a
lattice-derived account of differential object marking checked against the
[aissen-2003] DOM profiles, and the paper's engagement with [dowty-1991]'s
Argument Selection Principle. The DOM substrate reconstructs the
referential-property treatment the paper attributes to [grimm-2005].

## Main results

- `subject_region_iff_causation` / `kill_subject_range`: for every
  [dowty-1991] profile the subject is NOM/ERG iff it entails causation, and
  every node above *kill*'s minimal agent qualifies — both from the
  substrate's interval characterization of the regions.
- `russian_dom_matches_lattice` / `spanish_dom_within_lattice` /
  `animate_dom_object_is_dative_node`: the lattice predicts DOM for exactly
  {animate, human}, and the animate DOM object is literally the dative node.
- `domPredicted_monotone`, `latticeDOM_isMonotone`,
  `latticeDOM_matches_aissen_type2`: the lattice derives [aissen-2003]'s
  monotonicity universal and reproduces OT Type 2.
- `genitive_requires_entailment_free`: only the entailment-free object
  profile reaches the genitive node — the §5.2 intensionality restriction
  as a theorem over all [dowty-1991] profiles.
- `wellFormedPair_not_preserved`, `kiss_outranking_from_dominance`,
  `arrive_cross_theory`: what the lattice projection of Dowty's profiles
  loses, and the ASP re-derived from dominance
  (`outranks_of_lattice_dominance`) rather than checked per verb.
- `lattice_diverges_from_dependent_case`: the semantic-case vs
  structural-case fault line on animate objects, made explicit against the
  dependent-case pipeline in `Studies/Aissen2003.lean`.
-/

namespace Grimm2011

open ArgumentStructure
open ArgumentStructure
open Features.Prominence
open Aissen2003

/-! ### The canonical verb chain (§2.2, p.523–524)

Subjects populating a maximal chain: positional verbs at ⊥, then know/see
(sentience), discover (+instigation), look at (+motion), assassinate
(+volition, = ⊤). -/

/-- sit/stand subject: ⊥, p.523. -/
def sitAgentivity : Agentivity := ⊥

/-- know/see subject: sentience only, p.523–524. -/
def knowAgentivity : Agentivity := .mk false true false false

/-- discover subject: sentience + instigation, p.524. -/
def discoverAgentivity : Agentivity := .mk false true true false

/-- look at subject: sentience + instigation + motion, p.524. -/
def lookAtAgentivity : Agentivity := .mk false true true true

/-- assassinate subject: all four features, p.524. -/
def assassinateAgentivity : Agentivity := ⊤

/-- Each verb adds one feature: a strict chain from ⊥ to ⊤. -/
theorem canonical_verb_chain :
    sitAgentivity < knowAgentivity ∧ knowAgentivity < discoverAgentivity ∧
    discoverAgentivity < lookAtAgentivity ∧
    lookAtAgentivity < assassinateAgentivity := by decide

/-- All chain positions satisfy volition → sentience. -/
theorem canonical_verbs_valid :
    sitAgentivity.Valid ∧ knowAgentivity.Valid ∧ discoverAgentivity.Valid ∧
    lookAtAgentivity.Valid ∧ assassinateAgentivity.Valid := by decide

/-- The perception template's subject projects to exactly the know/see
    node — the [dowty-1991] bridge lands on the chain. -/
theorem see_subject_agentivity :
    Agentivity.fromEntailmentProfile perception.subjectProfile
      = knowAgentivity := rfl

/-! ### Tsunoda's transitivity hierarchy (§3, example 8)

Resultative Effective Action (kill, break) >> Contact (shoot, hit) >>
Pursuit (search, seek): the lower the patient's persistence, the more
prototypically transitive the verb. -/

/-- Class I/II patients are in the transitivity region; Class III (pursuit)
    is outside. -/
theorem tsunoda_region_membership :
    (TransitivityRank.resultativeEffective.patientType).InTransitiveRegion ∧
    (TransitivityRank.contact.patientType).InTransitiveRegion ∧
    ¬ (TransitivityRank.pursuit.patientType).InTransitiveRegion := by decide

/-- Patient nodes are ordered III ≤ I ≤ II: lower persistence, more
    affected. -/
theorem tsunoda_patient_chain :
    TransitivityRank.pursuit.patientType ≤
      TransitivityRank.resultativeEffective.patientType ∧
    TransitivityRank.resultativeEffective.patientType ≤
      TransitivityRank.contact.patientType := by decide

/-- Fig. 5 placements: the shared agent (Ia/IIa) is NOM/ERG; Class I/II
    patients are ACC/ABS; the pursuit patient falls outside the core
    object region. -/
theorem tsunoda_case_regions :
    effectorAgent.toCaseRegion = .nomErg ∧
    (TransitivityRank.resultativeEffective.patientType).toCaseRegion
      = .accAbs ∧
    (TransitivityRank.contact.patientType).toCaseRegion = .accAbs ∧
    (TransitivityRank.pursuit.patientType).toCaseRegion = .oblique := by
  decide

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
    (ParticipantType.fromSubjectProfile mannerContact.subjectProfile).toCaseRegion
      = .nomErg ∧
    (ParticipantType.fromObjectProfile contactObject).toCaseRegion = .oblique := by
  decide

/-- kick/eat objects are in the transitivity region; build objects (not
    existing at event start, p.529–530) are not. -/
theorem kick_object_in_region :
    (ParticipantType.fromObjectProfile contactObject).InTransitiveRegion ∧
    (ParticipantType.fromObjectProfile consumptionObject).InTransitiveRegion ∧
    ¬ (ParticipantType.fromObjectProfile creationObject).InTransitiveRegion := by
  decide

/-- build: subject → NOM/ERG; the created object (`exPersEnd`) → oblique. -/
theorem build_case_regions :
    (ParticipantType.fromSubjectProfile creation.subjectProfile).toCaseRegion
      = .nomErg ∧
    (ParticipantType.fromObjectProfile creationObject).toCaseRegion = .oblique := by
  decide

/-- eat: subject → NOM/ERG; the consumed object → ACC/ABS, with destroyed
    objects. -/
theorem eat_case_regions :
    (ParticipantType.fromSubjectProfile consumption.subjectProfile).toCaseRegion
      = .nomErg ∧
    (ParticipantType.fromObjectProfile consumptionObject).toCaseRegion
      = .accAbs := by decide

/-- buy/sell: subject → NOM/ERG. Buyer and seller share one profile — the
    [dowty-1991] §3.2 alternation tie. -/
theorem possessionTransfer_case_region :
    (ParticipantType.fromSubjectProfile possessionTransfer.subjectProfile).toCaseRegion
      = .nomErg := by decide

/-- see: sentience without instigation → oblique. Experiencer *subjects*
    land outside the dative region — `fromSubjectProfile` fixes total
    persistence, the dative region needs `quPersBeginning`. -/
theorem see_case_region :
    (ParticipantType.fromSubjectProfile perception.subjectProfile).toCaseRegion
      = .oblique := by decide

/-- run: volition + sentience + motion without instigation → oblique,
    matching unergative behaviour in split-S systems. -/
theorem run_case_region :
    (ParticipantType.fromSubjectProfile selfMotion.subjectProfile).toCaseRegion
      = .oblique := by decide

/-- arrive: motion only → oblique. -/
theorem arrive_case_region :
    (ParticipantType.fromSubjectProfile directedMotion.subjectProfile).toCaseRegion
      = .oblique := by decide

/-- die: the sole argument, read as patient, → ACC/ABS; ergative readout
    ABS — the unaccusative pattern. -/
theorem die_case_region :
    (ParticipantType.fromObjectProfile disappearance.subjectProfile).toCaseRegion
      = .accAbs ∧
    (ParticipantType.fromObjectProfile disappearance.subjectProfile).toCaseRegion.toErgativeCase
      = .abs := by decide

/-- **Instigation exactly divides the subjects**: for every [dowty-1991]
    profile, the subject lands in NOM/ERG iff it entails causation —
    the per-verb facts above are instances. From the interval
    characterization and `Agentivity.le_iff`, not enumeration. -/
theorem subject_region_iff_causation (p : EntailmentProfile) :
    (ParticipantType.fromSubjectProfile p).toCaseRegion = .nomErg ↔
      p.causation = true := by
  rw [ParticipantType.toCaseRegion_eq_nomErg_iff]
  constructor
  · exact fun h => ((Agentivity.le_iff _ _).mp h.1).2.2.1 rfl
  · intro hc
    exact ⟨(Agentivity.le_iff _ _).mpr
      ⟨fun h => Bool.noConfusion h, fun h => Bool.noConfusion h,
       fun _ => hc, fun h => Bool.noConfusion h⟩, le_refl _⟩

/-! ### Acceptable-argument ranges (§2.3, p.528)

Argument acceptability is closure-based: any node above a verb's minimal
agent requirement qualifies. Since *kill*'s agent requires only instigation,
its subject range at total persistence is the whole NOM/ERG interval — from
natural forces to intentional agents. -/

/-- Everything above *kill*'s minimal agent is NOM/ERG: upward closure plus
    the interval characterization `toCaseRegion_eq_nomErg_iff`. -/
theorem kill_subject_range {n : ParticipantType} (h : minimalInstigator ≤ n) :
    n.toCaseRegion = .nomErg :=
  (ParticipantType.toCaseRegion_eq_nomErg_iff n).mpr h

/-- The range's endpoints, derived: electricity (instigation only) and the
    assassin (⊤) are both acceptable *kill*-subjects. -/
theorem kill_subject_endpoints :
    minimalInstigator.toCaseRegion = .nomErg ∧
    (⊤ : ParticipantType).toCaseRegion = .nomErg :=
  ⟨kill_subject_range le_rfl, kill_subject_range le_top⟩

/-! ### Accusative and ergative alignment (§4, Fig. 6) -/

/-- The poles read out to the core markers of both systems: NOM/ACC in an
    accusative alignment, ERG/ABS in an ergative one. -/
theorem pole_alignment :
    maximalAgent.toCaseRegion.toAccusativeCase = .nom ∧
    maximalPatient.toCaseRegion.toAccusativeCase = .acc ∧
    maximalAgent.toCaseRegion.toErgativeCase = .erg ∧
    maximalPatient.toCaseRegion.toErgativeCase = .abs := by decide

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
def animacyToAgentivity : AnimacyLevel → Agentivity
  | .human     => .mk true true false false
  | .animate   => .mk false true false false
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
    ParticipantType :=
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

/-- The animate DOM object at `quPersBeginning` IS `sentientNonInstigator`
    — one lattice point shared with recipients and experiencers (Fig. 7).
    On this account DOM marking is dative marking (Spanish *a*). -/
theorem animate_dom_object_is_dative_node :
    objectNodeWithAnimacy .animate .quPersBeginning
      = sentientNonInstigator := rfl

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

/-- Accomplishment (kill-type) verbs: NOM/ERG subject and ACC/ABS object —
    maximal contrast (*matar*). Perception verbs lose the contrast on the
    subject side (`see_case_region`: oblique, *ver*); creation verbs have
    NOM/ERG subjects (`build_case_regions`) but no DOM question at all
    (`creation_dom_inapplicable`). -/
theorem kill_type_maximal_contrast :
    (ParticipantType.fromSubjectProfile accomplishmentSubjectProfile).toCaseRegion
      = .nomErg ∧
    (ParticipantType.fromObjectProfile accomplishmentObjectProfile).toCaseRegion
      = .accAbs := by decide

/-! ### The Russian genitive/accusative alternation (§5.2, Fig. 8)

Objects of intensional verbs (*want*, *seek*, *await*; p.539–541) take
accusative under the specific reading and genitive under the non-specific
one — a case contrast between two lattice nodes. -/

/-- The specific reading (object exists, `exPersBeginning`) sits in
    ACC/ABS; the non-specific reading (existence not entailed) is the
    lattice bottom — Grimm's governed genitive at "the lowest node of the
    lattice" (p.540). -/
theorem genAcc_reading_regions :
    (⟨⊥, .exPersBeginning⟩ : ParticipantType).toCaseRegion = .accAbs ∧
    (⟨⊥, .totalNonPersistence⟩ : ParticipantType) = ⊥ :=
  ⟨by decide, rfl⟩

/-- Only the entailment-free P-Patient profile reaches the genitive node:
    the lattice form of "the alternation is limited to intensional verbs"
    (p.541), for every [dowty-1991] profile. -/
theorem genitive_requires_entailment_free (p : EntailmentProfile) :
    PersistenceLevel.fromPatientProfile p = .totalNonPersistence ↔
      p.changeOfState = false ∧ p.incrementalTheme = false ∧
      p.causallyAffected = false ∧ p.stationary = false ∧
      p.dependentExistence = false := by
  rcases p with ⟨v, s, c, m, ie, cos, it, ca, st, de⟩
  cases v <;> cases s <;> cases c <;> cases m <;> cases ie <;>
    cases cos <;> cases it <;> cases ca <;> cases st <;> cases de <;> decide

/-- Limitation: [dowty-1991] (30e) codes de-dicto objects (*needs a car*)
    with dependent existence, which the bridge reads as destruction — the
    desire-class object lands at `exPersBeginning`, not at Grimm's ⊥
    placement for *want*. Dowty's features cannot separate "never entailed
    to exist" from "ceases to exist". -/
theorem desire_object_bridge_tension :
    desire.objectProfile.map PersistenceLevel.fromPatientProfile
      = some .exPersBeginning := rfl

/-! ### Grimm vs [dowty-1991]

§2.1 recasts Dowty's ten entailments as four agentivity features plus
persistence; the projection kernel is
`Agentivity.fromEntailmentProfile_eq_iff`. Below: what the recast loses
(Dowty's pairing constraints) and what it fixes (the *arrive* anomaly) —
cross-theory checks absorbed from `Studies/Dowty1991.lean`, since the
comparison belongs to the later paper. -/

/-- Dowty's `WellFormedPair` is invisible to the projection: a {C} and a
    {C, IE} subject project to the same node (IE is dropped,
    `Agentivity.fromEntailmentProfile_eq_iff`), yet against a {CoS}
    object only the first satisfies the IE→DE pairing constraint. -/
theorem wellFormedPair_not_preserved :
    WellFormedPair { causation := true } { changeOfState := true } ∧
    ¬ WellFormedPair { causation := true, independentExistence := true }
        { changeOfState := true } ∧
    ParticipantType.fromSubjectProfile { causation := true }
      = ParticipantType.fromSubjectProfile
          { causation := true, independentExistence := true } := by decide

/-- The *arrive* anomaly resolved: Table 1, the priority ASP, and the
    lattice all say unaccusative; only flat counting diverges. -/
theorem arrive_cross_theory :
    Dowty1991.table1 directedMotion.subjectProfile.volition
        directedMotion.subjectProfile.changeOfState = .unaccusative ∧
    PredictsUnaccusative directedMotion.subjectProfile ∧
    Dowty1991.flatPredictsUnaccusative directedMotion.subjectProfile = false ∧
    (ParticipantType.fromSubjectProfile directedMotion.subjectProfile).toCaseRegion
      ≠ .nomErg := by decide

/-- kick: ASP outranking and the lattice's subject region agree — NOM
    subject. -/
theorem kick_asp_grimm_consistent :
    OutranksForSubject mannerContact.subjectProfile contactObject ∧
    (ParticipantType.fromSubjectProfile mannerContact.subjectProfile).toCaseRegion.toAccusativeCase
      = .nom := by decide

/-- die: priority ASP, flat counting, and the lattice agree on
    unaccusativity. -/
theorem die_asp_grimm_consistent :
    PredictsUnaccusative disappearance.subjectProfile ∧
    Dowty1991.flatPredictsUnaccusative disappearance.subjectProfile = true ∧
    (ParticipantType.fromObjectProfile disappearance.subjectProfile).toCaseRegion
      = .accAbs := by decide

/-- kiss: the subject strictly dominates the object on the lattice —
    `Dowty1991.kiss_asymmetry_is_volition` as order. -/
theorem kiss_subject_dominates :
    Agentivity.fromEntailmentProfile Dowty1991.kissObjectProfile <
      Agentivity.fromEntailmentProfile Dowty1991.kissSubjectProfile := by
  decide

/-- Subject selection for *kiss* from lattice dominance alone
    (`outranks_of_lattice_dominance`): the ASP mechanized, re-deriving
    `Dowty1991.kiss_subject_outranks` without counting or `decide`. -/
theorem kiss_outranking_from_dominance :
    OutranksForSubject Dowty1991.kissSubjectProfile
      Dowty1991.kissObjectProfile :=
  outranks_of_lattice_dominance _ _ kiss_subject_dominates fun _ => rfl

/-- Dowty's count comparison follows from lattice dominance via
    `featureCount_monotone` and `pAgentScore_decomposition`. -/
theorem kiss_flat_count_from_lattice :
    Dowty1991.kissObjectProfile.pAgentScore ≤
      Dowty1991.kissSubjectProfile.pAgentScore := by
  rw [pAgentScore_decomposition, pAgentScore_decomposition]
  exact Nat.add_le_add
    (Agentivity.featureCount_monotone kiss_subject_dominates.le) le_rfl

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

end Grimm2011
