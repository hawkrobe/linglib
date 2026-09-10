import Linglib.Semantics.ArgumentStructure.CaseRegion
import Linglib.Semantics.ArgumentStructure.Projection
import Linglib.Semantics.ArgumentStructure.RoleList
import Linglib.Studies.Dowty1991

/-!
# Grimm (2011): Semantics of Case

This file formalizes [grimm-2011]'s account of case assignment over the agentivity lattice of
`Semantics/ArgumentStructure/`: [dowty-1991]'s proto-role entailments recast as four privative
agentivity properties and a persistence axis, whose product orders participant types by semantic
prominence, with a case a connected region of that lattice. The canonical subjects of section 2.2
climb a chain from the positional verbs to *assassinate* (`canonical_verb_chain`), and the
acceptable arguments of a predicate are closed upward for agents and downward for patients, so
that natural forces kill and the object of *hit* may be unaffected or destroyed but must exist
when the event begins (`kill_subject_range`, `transitive_region_eq_Ici`); the dominance
criterion for subject selection reproduces [dowty-1991]'s choice for *kiss*
(`kiss_outranking_from_dominance`). Section 3 maps [tsunoda-1985]'s effectiveness hierarchy: the
agent of *break*, *shoot*, and *search* keeps instigation and motion while the patient rises
from existential persistence through qualitative persistence and out of the transitivity
region (`transitivity_hierarchy`). Section 4 reads the two core cases of either alignment off
the poles (`pole_alignment`), section 5.1 places the recipient, the dative experiencer, and the
dative object of *danken* and *helfen* at one node of the dative region (`recipient_dative`), and
section 5.2 derives the Russian genitive/accusative alternation of *ždat'* 'wait for' from
referentiality: a referring object exists when the event begins and falls in the accusative
region, a non-specific one may stay at the bottom node that the governed genitive marks, and
only a verb without existential persistence entailments on its object leaves that node open
(`genitive_accusative_alternation`, `genitive_outside_region`).

## Implementation notes

The lattice, the named participant types, the case regions, and the projection from
[dowty-1991]'s profiles are substrate; this file supplies the paper's placements and reads its
predictions off the interval characterizations of the regions. The paper's remarks on
differential object marking (the interaction of verbal and referential properties, deferred to
[grimm-2005]) and on the size of the nominative or ergative region in a given language are not
formalized. Definiteness is the paper's three-step hierarchy (14), with the referring feature the
one that entails existence.

## References

* [grimm-2011]
* [dowty-1991]
* [tsunoda-1985]
* [grimm-2005]
* [fillmore-1968]
-/

namespace Grimm2011

open ArgumentStructure

/-! ### The canonical verb chain, section 2.2 -/

/-- The subject of the positional verbs *sit* and *stand*: no agentivity property. -/
def sitAgentivity : Agentivity := ⊥

/-- The subject of *know* and *see*: sentience. -/
def knowAgentivity : Agentivity := .mk false true false false

/-- The subject of *discover*: sentience and instigation. -/
def discoverAgentivity : Agentivity := .mk false true true false

/-- The subject of *look at*: sentience, instigation, and motion. -/
def lookAtAgentivity : Agentivity := .mk false true true true

/-- The subject of *assassinate*: all four properties. -/
def assassinateAgentivity : Agentivity := ⊤

/-- Each verb adds one property to the last: a chain from the bottom to the top of the
agentivity lattice, the paper's illustration that height is degree of agentivity. -/
theorem canonical_verb_chain :
    sitAgentivity < knowAgentivity ∧ knowAgentivity < discoverAgentivity ∧
      discoverAgentivity < lookAtAgentivity ∧ lookAtAgentivity < assassinateAgentivity := by
  decide

/-- Every node of the chain respects the one relation among the properties, volition
entails sentience. -/
theorem canonical_verbs_valid :
    sitAgentivity.Valid ∧ knowAgentivity.Valid ∧ discoverAgentivity.Valid ∧
      lookAtAgentivity.Valid ∧ assassinateAgentivity.Valid := by
  decide

/-- The projection of [dowty-1991]'s perception profile lands on the chain at *see*. -/
theorem see_subject_agentivity :
    Agentivity.fromEntailmentProfile perception.subjectProfile = knowAgentivity := rfl

/-! ### Argument ranges and subject selection, section 2.3

The agent of *kill* need only instigate, so natural forces such as electricity and eventive
nominals such as the explosion are acceptable subjects, and so is every node above them: agents
are upward closed. The patient of *hit* canonically changes qualitatively, but the object of the
conative *hit at* is unaffected and an object may happen to be destroyed, while an entity that
does not exist when the event begins cannot be hit: patients are closed downward to the
existence of the entity. -/

/-- Everything above the minimal instigator is in the nominative or ergative region: the range of
the subject of *kill*, from the interval characterization of that region. -/
theorem kill_subject_range {n : ParticipantType} (h : minimalInstigator ≤ n) :
    n.toCaseRegion = .nomErg :=
  (ParticipantType.toCaseRegion_eq_nomErg_iff n).mpr h

/-- The endpoints of the range: electricity, with instigation alone, and the assassin. -/
theorem kill_subject_endpoints :
    minimalInstigator.toCaseRegion = .nomErg ∧ (⊤ : ParticipantType).toCaseRegion = .nomErg :=
  ⟨kill_subject_range le_rfl, kill_subject_range le_top⟩

/-- The persistence levels an entity that exists when the event begins can have are the up-set
of existential persistence (beginning): the range of the patient of *hit* and, in section 3, the
persistence axis of the transitivity region. -/
theorem transitive_region_eq_Ici (n : ParticipantType) :
    n.InTransitiveRegion ↔ PersistenceLevel.exPersBeginning ≤ n.persistence := by
  revert n; decide

/-- The subject of *kiss* strictly dominates its object on the agentivity lattice, so the
dominance criterion selects it, [dowty-1991]'s result for (43) without counting entailments. -/
theorem kiss_outranking_from_dominance :
    OutranksForSubject Dowty1991.kissSubjectProfile Dowty1991.kissObjectProfile :=
  outranks_of_lattice_dominance _ _ (by decide) (by decide)

/-! ### The transitivity region and the effectiveness hierarchy, section 3

[tsunoda-1985]'s hierarchy, the paper's (8): resultative effective action verbs (*break*) above
contact verbs (*shoot*) above pursuit verbs (*search*). The agent of the first two classes
entails instigation and motion; the agent of pursuit adds sentience (Fig. 5). -/

/-- The agent of *search*, Fig. 5's IIIa: instigation, motion, and sentience at total
persistence. -/
def pursuitAgent : ParticipantType := ⟨.mk false true true true, .totalPersistence⟩

/-- The hierarchy as a progression of the patient away from the maximal patient: the patient
of *break* is the maximal patient, that of *shoot* lies above it inside the transitivity region,
that of *search* outside it, while the agents stay in the nominative or ergative region. -/
theorem transitivity_hierarchy :
    TransitivityRank.resultativeEffective.patientType = maximalPatient ∧
      TransitivityRank.resultativeEffective.patientType ≤ TransitivityRank.contact.patientType ∧
      TransitivityRank.resultativeEffective.patientType ≠ TransitivityRank.contact.patientType ∧
      TransitivityRank.contact.patientType.InTransitiveRegion ∧
      ¬ TransitivityRank.pursuit.patientType.InTransitiveRegion ∧
      effectorAgent.toCaseRegion = .nomErg ∧ pursuitAgent.toCaseRegion = .nomErg := by
  decide

/-- The patients of the two effective classes fall in the accusative or absolutive region and the
pursuit patient does not. -/
theorem transitivity_patient_regions :
    TransitivityRank.resultativeEffective.patientType.toCaseRegion = .accAbs ∧
      TransitivityRank.contact.patientType.toCaseRegion = .accAbs ∧
      TransitivityRank.pursuit.patientType.toCaseRegion ≠ .accAbs := by
  decide

/-! ### Core case marking systems, section 4 -/

/-- Fig. 6: the maximal agent and the maximal patient read out to the two core cases of either
alignment, nominative and accusative or ergative and absolutive. -/
theorem pole_alignment :
    maximalAgent.toCaseRegion.toAccusativeCase = .nom ∧
      maximalPatient.toCaseRegion.toAccusativeCase = .acc ∧
      maximalAgent.toCaseRegion.toErgativeCase = .erg ∧
      maximalPatient.toCaseRegion.toErgativeCase = .abs := by
  decide

/-! ### Extensions of the dative, section 5.1

The recipient of *geben* (9) is consciously involved as a possessor and qualitatively changed in
its possessions; the dative experiencer of the Urdu *ghussa aana* 'get angry' (10) is sentient and
undergoes a psychological change; the second argument of *danken* and *gratulieren* undergoes
caused possession in the cognitive realm and that of *dienen* and *helfen* a change through the
benefit conferred. All three require sentience at qualitative persistence (beginning), the
substrate's `sentientNonInstigator`. -/

/-- The recipient of (9). -/
def recipient : ParticipantType := sentientNonInstigator

/-- The recipient's node is in the dative region, and with it the experiencer and the second
argument of the two-place verbs that share its entailments (Fig. 7). -/
theorem recipient_dative : recipient.toCaseRegion = .dative := by decide

/-! ### The genitive/accusative alternation in Russian, section 5.2

*Ivan ždët tramvaj* (accusative) 'Ivan is waiting for the/a certain tram' against *Ivan ždët
tramvaja* (genitive) 'Ivan is waiting for a tram', (12). The governed genitive marks the entity
whose existence is not entailed, the bottom node of the lattice; the accusative region contains
the node of existential persistence (beginning). An opacity-creating verb entails nothing for
its object, so the noun phrase decides: a referring one exists when the event begins. -/

/-- The definiteness hierarchy (14): a specific indefinite is referring, a definite referring and
given, a non-specific indefinite neither. -/
inductive Definiteness where
  | nonSpecificIndefinite
  | specificIndefinite
  | definite
  deriving DecidableEq, Repr

/-- The referring feature of (14a). -/
def Definiteness.Referring (d : Definiteness) : Prop := d ≠ .nonSpecificIndefinite

instance (d : Definiteness) : Decidable d.Referring := inferInstanceAs (Decidable (_ ≠ _))

/-- The lowest node an object of an opacity-creating verb can occupy with a noun phrase of the
given definiteness: the maximal patient once existence is entailed, the bottom otherwise. -/
def opacityObject (d : Definiteness) : ParticipantType :=
  if d.Referring then maximalPatient else ⊥

/-- (12): the object is in the accusative region exactly when the noun phrase refers; the
non-specific reading stays at the bottom node, the governed genitive's. -/
theorem genitive_accusative_alternation (d : Definiteness) :
    ((opacityObject d).toCaseRegion = .accAbs ↔ d.Referring) ∧
      (opacityObject d = ⊥ ↔ ¬ d.Referring) := by
  cases d <;> decide

/-- The alternation is limited to verbs without existential persistence entailments on their
object: any node inside the transitivity region lies above the genitive's. -/
theorem genitive_outside_region (n : ParticipantType) (h : n.InTransitiveRegion) :
    n ≠ ⊥ :=
  λ hn => absurd h (hn ▸ by decide)

end Grimm2011
