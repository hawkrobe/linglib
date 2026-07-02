/-!
# Proto-role entailment profiles

[dowty-1991] [grimm-2011] [davis-koenig-2000] [levin-2019]

An `EntailmentProfile` records which of [dowty-1991]'s ten proto-role
entailments (pp.572–573) a verb imposes on one of its arguments. Proto-Agent
and Proto-Patient are cluster concepts: each is a set of entailments, and an
argument's degree of agenthood or patienthood is the set it satisfies. The
Argument Selection Principle is stated lattice-theoretically ([grimm-2011]):
subjecthood tracks strict superset dominance on Proto-Agent feature sets,
with Proto-Patient dominance breaking ties.

## Main declarations

- `EntailmentProfile` — the ten Boolean entailment fields
- `EntailmentProfile.pAgentScore`, `EntailmentProfile.pPatientScore` —
  flat feature counts
- `PAgentDominates`, `PPatientDominates` — subset ordering on feature sets
- `OutranksForSubject` — the lattice-based Argument Selection Principle
- `PredictsUnaccusative`, `PredictsUnergative` — split-intransitivity
  predictions
- `kickSubjectProfile` … `accomplishmentObjectProfile` — canonical per-verb
  and per-template profiles

## Implementation notes

The ten entailments are not independent ([levin-2019] §2.1): volition
presupposes sentience (`EntailmentProfile.WellFormedInternal`); causation,
movement, and independent existence pair asymmetrically with Proto-Patient
entailments (`WellFormedPair`); and the affectedness-related Proto-Patient
entailments form an implicational hierarchy ([beavers-2010]). Their algebraic
counterparts live in `AgentivityLattice.lean`. [dowty-1991]'s original
flat-counting selection principle is preserved for comparison in
`Studies/Dowty1991.lean`; the counting accessors here are informational only.
Causation priority ([davis-koenig-2000]) needs no extra clause: it falls out
of feature-set inclusion.
-/

namespace Semantics.ArgumentStructure.EntailmentProfile

/-- The ten entailments defining the proto-roles ([dowty-1991] pp.572–573):
the first five are Proto-Agent, the last five Proto-Patient. Fields default
to `false`, so a profile lists only the entailments it imposes. -/
structure EntailmentProfile where
  /-- Volitional involvement in the event. -/
  volition : Bool := false
  /-- Sentience or perception. -/
  sentience : Bool := false
  /-- Causes an event or change of state in another participant. -/
  causation : Bool := false
  /-- Movement relative to another participant. -/
  movement : Bool := false
  /-- Exists independently of the event named by the verb. -/
  independentExistence : Bool := false
  /-- Undergoes a change of state. -/
  changeOfState : Bool := false
  /-- Incremental theme: the argument measures out the event. -/
  incrementalTheme : Bool := false
  /-- Causally affected by another participant. -/
  causallyAffected : Bool := false
  /-- Stationary relative to another participant. -/
  stationary : Bool := false
  /-- Does not exist independently of the event. -/
  dependentExistence : Bool := false
  deriving DecidableEq, Repr

variable (p q subj obj : EntailmentProfile)

/-! ### Feature counting -/

/-- Number of Proto-Agent entailments. Informational: the Argument Selection
Principle uses lattice comparison ([grimm-2011]), not counting. -/
def EntailmentProfile.pAgentScore : Nat :=
  p.volition.toNat + p.sentience.toNat + p.causation.toNat +
  p.movement.toNat + p.independentExistence.toNat

/-- Number of Proto-Patient entailments. -/
def EntailmentProfile.pPatientScore : Nat :=
  p.changeOfState.toNat + p.incrementalTheme.toNat +
  p.causallyAffected.toNat + p.stationary.toNat +
  p.dependentExistence.toNat

/-! ### Lattice comparison -/

/-- `p` has every Proto-Agent feature that `q` has: the subset ordering on
Proto-Agent feature sets. -/
def PAgentDominates : Prop :=
  (q.volition = true → p.volition = true) ∧
  (q.sentience = true → p.sentience = true) ∧
  (q.causation = true → p.causation = true) ∧
  (q.movement = true → p.movement = true) ∧
  (q.independentExistence = true → p.independentExistence = true)

instance : Decidable (PAgentDominates p q) := by
  unfold PAgentDominates; infer_instance

/-- `p` has every Proto-Patient feature that `q` has. -/
def PPatientDominates : Prop :=
  (q.changeOfState = true → p.changeOfState = true) ∧
  (q.incrementalTheme = true → p.incrementalTheme = true) ∧
  (q.causallyAffected = true → p.causallyAffected = true) ∧
  (q.stationary = true → p.stationary = true) ∧
  (q.dependentExistence = true → p.dependentExistence = true)

instance : Decidable (PPatientDominates p q) := by
  unfold PPatientDominates; infer_instance

/-- `p`'s Proto-Agent feature set is a strict superset of `q`'s. -/
def PAgentStrictlyDominates : Prop :=
  PAgentDominates p q ∧ ¬ PAgentDominates q p

instance : Decidable (PAgentStrictlyDominates p q) := by
  unfold PAgentStrictlyDominates; infer_instance

/-- `p`'s Proto-Patient feature set is a strict superset of `q`'s. -/
def PPatientStrictlyDominates : Prop :=
  PPatientDominates p q ∧ ¬ PPatientDominates q p

instance : Decidable (PPatientStrictlyDominates p q) := by
  unfold PPatientStrictlyDominates; infer_instance

theorem pAgentDominates_refl : PAgentDominates p p :=
  ⟨id, id, id, id, id⟩

theorem pPatientDominates_refl : PPatientDominates p p :=
  ⟨id, id, id, id, id⟩

/-! ### Argument selection -/

/-- The lattice-based Argument Selection Principle ([grimm-2011],
[davis-koenig-2000]): `subj` outranks `obj` for subjecthood iff `subj`
strictly Proto-Agent-dominates `obj`, or the two are Proto-Agent-incomparable
and `obj` strictly Proto-Patient-dominates `subj`. Causation priority is
structural: `{causation, IE}` strictly dominates `{IE}` yet is incomparable
with `{sentience, IE}`. -/
def OutranksForSubject : Prop :=
  PAgentStrictlyDominates subj obj ∨
  (¬ PAgentStrictlyDominates subj obj ∧ ¬ PAgentStrictlyDominates obj subj ∧
   PPatientStrictlyDominates obj subj)

instance : Decidable (OutranksForSubject subj obj) := by
  unfold OutranksForSubject; infer_instance

/-- [dowty-1991]'s Corollary 1 (p.579): neither argument outranks the other,
so subject choice may alternate (*buy*/*sell*, *like*/*please*). -/
def AllowsAlternation : Prop :=
  ¬ OutranksForSubject p q ∧ ¬ OutranksForSubject q p

instance : Decidable (AllowsAlternation p q) := by
  unfold AllowsAlternation; infer_instance

/-! ### Split intransitivity -/

/-- The sole argument lacks the priority Proto-Agent entailments — volition
and causation ([davis-koenig-2000]) — and bears at least one Proto-Patient
entailment ([dowty-1991] Table 1). Unlike flat counting, this classifies
*arrive* as unaccusative. -/
def PredictsUnaccusative : Prop :=
  p.volition = false ∧ p.causation = false ∧ p.pPatientScore > 0

instance : DecidablePred PredictsUnaccusative := λ p => by
  unfold PredictsUnaccusative; infer_instance

/-- The sole argument bears a priority Proto-Agent entailment (volition or
causation) and no Proto-Patient entailment. -/
def PredictsUnergative : Prop :=
  (p.volition = true ∨ p.causation = true) ∧ p.pPatientScore = 0

instance : DecidablePred PredictsUnergative := λ p => by
  unfold PredictsUnergative; infer_instance

/-! ### Well-formedness -/

/-- Volition presupposes sentience: only sentient entities can act
volitionally ([dowty-1991] p.607, [levin-2019] §2.1). -/
def EntailmentProfile.WellFormedInternal : Prop :=
  p.volition = true → p.sentience = true

instance : DecidablePred EntailmentProfile.WellFormedInternal := λ p => by
  unfold EntailmentProfile.WellFormedInternal; infer_instance

/-- Three Proto-Agent entailments pair asymmetrically across a
subject–object pair ([davis-koenig-2000], [primus-1999]): causation →
changeOfState, movement → stationary, independentExistence →
dependentExistence. -/
def WellFormedPair : Prop :=
  (subj.causation = true → obj.changeOfState = true) ∧
  (subj.movement = true → obj.stationary = true) ∧
  (subj.independentExistence = true → obj.dependentExistence = true)

instance : Decidable (WellFormedPair subj obj) := by
  unfold WellFormedPair; infer_instance

/-! ### The do-test -/

/-- The *do*-test ([cruse-1973] via [dowty-1991]) passes on semantic grounds
iff the profile entails volition, causation, or movement. -/
def PassesDoTestFromProfile : Prop :=
  p.volition = true ∨ p.causation = true ∨ p.movement = true

instance : DecidablePred PassesDoTestFromProfile := λ p => by
  unfold PassesDoTestFromProfile; infer_instance

/-! ### Effectors and force recipients -/

/-- A self-energetic force bearer ([van-valin-wilkins-1996]): movement plus
independent existence, realized as external argument. -/
def IsEffector : Prop :=
  p.movement = true ∧ p.independentExistence = true

instance : DecidablePred IsEffector := λ p => by
  unfold IsEffector; infer_instance

/-- Causally affected or stationary, realized as internal argument. -/
def IsForceRecipient : Prop :=
  p.causallyAffected = true ∨ p.stationary = true

instance : DecidablePred IsForceRecipient := λ p => by
  unfold IsForceRecipient; infer_instance

/-- An effector carries at least two Proto-Agent entailments. -/
theorem two_le_pAgentScore_of_isEffector (h : IsEffector p) :
    2 ≤ p.pAgentScore := by
  simp [EntailmentProfile.pAgentScore, h.1, h.2]

/-! ### Canonical verb profiles

Canonical entailment content for specific verb senses, consumed by
`EventStructure.lean`, `Morphology/RootTypology.lean`, and study files. -/

/-- *kick* subject: prototypical agent (V+S+C+M+IE). -/
def kickSubjectProfile : EntailmentProfile :=
  { volition := true, sentience := true, causation := true, movement := true,
    independentExistence := true }

/-- *kick* object: CoS+CA+St. -/
def kickObjectProfile : EntailmentProfile :=
  { changeOfState := true, causallyAffected := true, stationary := true }

/-- *build* subject: V+S+C+M+IE. -/
def buildSubjectProfile : EntailmentProfile :=
  { volition := true, sentience := true, causation := true, movement := true,
    independentExistence := true }

/-- *build* object: CoS+IT+CA+DE (incremental theme, dependent existence). -/
def buildObjectProfile : EntailmentProfile :=
  { changeOfState := true, incrementalTheme := true, causallyAffected := true,
    dependentExistence := true }

/-- *see* subject: experiencer (S+IE). -/
def seeSubjectProfile : EntailmentProfile :=
  { sentience := true, independentExistence := true }

/-- *run* subject: V+S+M+IE (unergative). -/
def runSubjectProfile : EntailmentProfile :=
  { volition := true, sentience := true, movement := true,
    independentExistence := true }

/-- *arrive* subject: M+IE+CoS (unaccusative). -/
def arriveSubjectProfile : EntailmentProfile :=
  { movement := true, independentExistence := true, changeOfState := true }

/-- *die* subject: CoS+CA+DE (unaccusative). -/
def dieSubjectProfile : EntailmentProfile :=
  { changeOfState := true, causallyAffected := true, dependentExistence := true }

/-- *eat* subject: V+S+C+M+IE. -/
def eatSubjectProfile : EntailmentProfile :=
  { volition := true, sentience := true, causation := true, movement := true,
    independentExistence := true }

/-- *eat* object: CoS+IT+CA (incremental theme). -/
def eatObjectProfile : EntailmentProfile :=
  { changeOfState := true, incrementalTheme := true, causallyAffected := true }

/-- *buy* subject: V+S+C+IE. -/
def buySubjectProfile : EntailmentProfile :=
  { volition := true, sentience := true, causation := true,
    independentExistence := true }

/-- *sell* subject: V+S+C+IE (same as *buy*). -/
def sellSubjectProfile : EntailmentProfile :=
  { volition := true, sentience := true, causation := true,
    independentExistence := true }

/-- *sweep* basic-sense subject: M+IE only; underspecified for volition, so
agentivity is pragmatically resolved. -/
def sweepBasicSubjectProfile : EntailmentProfile :=
  { movement := true, independentExistence := true }

/-- *sweep* broom-sense subject: obligatory agent (V+S+C+M+IE); instrument
lexicalization forces volition, sentience, causation. -/
def sweepBroomSubjectProfile : EntailmentProfile :=
  { volition := true, sentience := true, causation := true, movement := true,
    independentExistence := true }

/-! ### Template-level proto-role defaults

Per-template subject/object defaults ([rappaport-hovav-levin-1998] with
[dowty-1991]'s entailments), consumed by `Template.subjectProfile` and
`Template.objectProfile` in `EventStructure.lean` and by Fragment-level verb
entries. -/

/-- State template subject: psych-state holder (*admire*, *want*) — S+IE. -/
def stateSubjectProfile : EntailmentProfile :=
  { sentience := true, independentExistence := true }

/-- Activity template subject: V+S+M+IE. Transitive activities like *hit*
add causation at the class level via root-contributed objects. -/
def activitySubjectProfile : EntailmentProfile :=
  { volition := true, sentience := true, movement := true,
    independentExistence := true }

/-- Achievement template subject: undergoes change (M+IE+CoS). -/
def achievementSubjectProfile : EntailmentProfile :=
  { movement := true, independentExistence := true, changeOfState := true }

/-- Accomplishment template subject: full proto-agent (V+S+C+M+IE). -/
def accomplishmentSubjectProfile : EntailmentProfile :=
  { volition := true, sentience := true, causation := true, movement := true,
    independentExistence := true }

/-- Accomplishment template object: result patient (CoS+CA). Incremental
themes (*eat*, *build*) add IT per-verb — not all accomplishment objects
measure the event. -/
def accomplishmentObjectProfile : EntailmentProfile :=
  { changeOfState := true, causallyAffected := true }

end Semantics.ArgumentStructure.EntailmentProfile
