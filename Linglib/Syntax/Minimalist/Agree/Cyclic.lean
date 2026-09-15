import Linglib.Syntax.Minimalist.Phi.Geometry
import Linglib.Syntax.Minimalist.Probe.Phi

/-!
# Cyclic Agree over articulated person probes

This file defines cyclic Agree over articulated person probes ([bejar-rezac-2009]). Person is
decomposed into privative segments in a containment hierarchy, every person bearing `π`, speech
act participants also `participant`, and the innermost segment, `speaker` or `addressee`,
distinguishing first from second person according to a geometry. A probe is an ordered list of
unvalued segments, and a language's agreement system is a geometry together with a probe. The
probe meets the internal argument first and checks every segment the argument bears; the
unmatched segments are its active residue, which meets the external argument on the next cycle.
The external argument controls the agreement slot when it checks some residue, a direct context,
and the internal argument controls it otherwise, an inverse context, in which the external
argument's person is unlicensed by the core probe.

An articulated probe is a family of flat relativized searches, one per segment, over the
cyclically ordered arguments, so the residue-based definitions factor through `Probe.search`
(`eaIsLicensed_iff_segment_licensed`, `cycleSegments_eq_segmentGoal_filters`).

## Main definitions

* `Minimalist.CyclicAgree.Segment`, `Minimalist.CyclicAgree.Geometry`,
  `Minimalist.CyclicAgree.personSpec`
* `Minimalist.Probe.Articulation`, `Minimalist.CyclicAgree.AgreementSystem`
* `Minimalist.CyclicAgree.activeResidue`, `Minimalist.CyclicAgree.agreementValue`,
  `Minimalist.CyclicAgree.cycleSegments`
* `Minimalist.CyclicAgree.isInverseContext`, `Minimalist.CyclicAgree.eaIsLicensed`

## Main results

* `Minimalist.CyclicAgree.plc_violation_iff_inverse`: the external argument is unlicensed
  exactly in inverse contexts.
* `Minimalist.CyclicAgree.same_person_ia_controls`, `Minimalist.CyclicAgree.flat_all_inverse`.

## References

* [bejar-rezac-2009]
* [harley-ritter-2002]
* [coon-keine-2021]
-/

namespace Minimalist.CyclicAgree

/-! ### Person segments and geometries -/

/-- A segment of an articulated person feature. Every person bears `pi`, speech act participants
also `participant`, and the innermost segments `speaker` and `addressee` distinguish first from
second person according to the geometry. -/
inductive Segment where
  | pi
  | participant
  | speaker
  | addressee
  deriving DecidableEq, Repr, Inhabited

/-- A person geometry fixes which innermost segment distinguishes first from second person.
Under `standard` first person is the most specified and bears `speaker`, under `addressee`
second person is and bears `addressee`, and under `branching` the two are sister leaves under
`participant` ([harley-ritter-2002]). -/
inductive Geometry where
  | standard
  | addressee
  | branching
  deriving DecidableEq, Repr

/-- The segments a person bears under a geometry. -/
def personSpec (geom : Geometry) : Person → List Segment
  | .third | .zero => [.pi]
  | .first | .firstInclusive | .firstExclusive => match geom with
    | .standard | .branching => [.pi, .participant, .speaker]
    | .addressee => [.pi, .participant]
  | .second => match geom with
    | .standard  => [.pi, .participant]
    | .addressee | .branching => [.pi, .participant, .addressee]

/-- Every person bears `pi` under every geometry. -/
theorem pi_mem_personSpec (geom : Geometry) (p : Person) : Segment.pi ∈ personSpec geom p := by
  cases geom <;> cases p <;> decide

/-- Under the standard geometry a person bears `participant` iff its decomposition does. -/
theorem std_participant_matches_decomposed (p : Person) :
    (personSpec .standard p).contains .participant = (decomposePerson p).hasParticipant := by
  cases p <;> decide

/-- Under the standard geometry the second person's segments are among the first person's. -/
theorem std_first_entails_second :
    ∀ s ∈ personSpec .standard .second, s ∈ personSpec .standard .first := by
  intro s hs; simp only [personSpec, List.mem_cons, List.mem_nil_iff] at hs ⊢
  rcases hs with rfl | rfl | h <;> simp_all

/-- Under the standard geometry the third person's segments are among the second person's. -/
theorem std_second_entails_third :
    ∀ s ∈ personSpec .standard .third, s ∈ personSpec .standard .second := by
  intro s hs; simp only [personSpec, List.mem_cons, List.mem_nil_iff] at hs ⊢
  rcases hs with rfl | h <;> simp_all

/-! ### Articulated probes and agreement systems -/

/-- An articulated probe is a list of unvalued segments, from the most general to the most
specific. -/
abbrev _root_.Minimalist.Probe.Articulation := List Segment

/-- The flat probe `[uπ]`, which any argument fully checks. -/
def flatProbe : Probe.Articulation := [.pi]

/-- The partial probe `[uπ, uParticipant]`, which distinguishes participants from third person
in every geometry. -/
def partialProbe : Probe.Articulation := [.pi, .participant]

/-- The full probe of the standard geometry, `[uπ, uParticipant, uSpeaker]`. -/
def fullProbeStd : Probe.Articulation := [.pi, .participant, .speaker]

/-- The full probe of the addressee geometry, `[uπ, uParticipant, uAddressee]`. -/
def fullProbeAddr : Probe.Articulation := [.pi, .participant, .addressee]

/-- A language's agreement system is a geometry together with the articulation of its probe. -/
structure AgreementSystem where
  /-- The person geometry. -/
  geometry : Geometry
  /-- The articulated probe. -/
  probe : Probe.Articulation
  deriving DecidableEq, Repr

/-! ### Cycles -/

/-- The active residue of a probe after Agree with a goal, the segments the goal does not
bear. -/
def activeResidue (probe : Probe.Articulation) (goal : List Segment) : Probe.Articulation :=
  probe.filter (fun s => !goal.contains s)

/-- The argument controlling the core agreement slot. -/
inductive Controller where
  | ia
  | ea
  deriving DecidableEq, Repr

/-- The external argument Agrees on the second cycle when it bears some segment of the residue
the internal argument left. -/
def eaAgrees (geom : Geometry) (probe : Probe.Articulation) (ea ia : Person) : Bool :=
  let residue := activeResidue probe (personSpec geom ia)
  let residueAfterEA := activeResidue residue (personSpec geom ea)
  residueAfterEA.length < residue.length

/-- The argument controlling the core slot, the external argument when it Agrees on the second
cycle and the internal argument otherwise. -/
def agreementController (geom : Geometry) (probe : Probe.Articulation) (ea ia : Person) :
    Controller :=
  if eaAgrees geom probe ea ia then .ea else .ia

/-- The person the core agreement slot realizes. -/
def agreementValue (geom : Geometry) (probe : Probe.Articulation) (ea ia : Person) : Person :=
  match agreementController geom probe ea ia with
  | .ea => ea
  | .ia => ia

/-- The controller under an agreement system. -/
def AgreementSystem.controller (sys : AgreementSystem) (ea ia : Person) : Controller :=
  agreementController sys.geometry sys.probe ea ia

/-- The agreement value under an agreement system. -/
def AgreementSystem.value (sys : AgreementSystem) (ea ia : Person) : Person :=
  agreementValue sys.geometry sys.probe ea ia

/-- The segments checked on each cycle, by the internal argument and then by the external
argument out of the residue. -/
def cycleSegments (geom : Geometry) (probe : Probe.Articulation) (ea ia : Person) :
    Probe.Articulation × Probe.Articulation :=
  let iaSpec := personSpec geom ia
  let cycleI := probe.filter (fun s => iaSpec.contains s)
  let residue := activeResidue probe iaSpec
  let eaSpec := personSpec geom ea
  let cycleII := residue.filter (fun s => eaSpec.contains s)
  (cycleI, cycleII)

/-- The probe is valued on two distinct cycles, the configuration behind second-cycle
morphology. -/
def hasSecondCycleEffect (geom : Geometry) (probe : Probe.Articulation) (ea ia : Person) :
    Bool :=
  let (c1, c2) := cycleSegments geom probe ea ia
  !c1.isEmpty && !c2.isEmpty

/-! ### Direct and inverse contexts -/

/-- An inverse context, in which the core probe never Agrees with the external argument,
either because the internal argument checks it fully or because the external argument bears no
segment of the residue. -/
def isInverseContext (geom : Geometry) (probe : Probe.Articulation) (ea ia : Person) : Bool :=
  !eaAgrees geom probe ea ia

/-- A direct context, in which the external argument checks some residue. -/
def isDirectContext (geom : Geometry) (probe : Probe.Articulation) (ea ia : Person) : Bool :=
  eaAgrees geom probe ea ia

/-- The context is inverse under an agreement system. -/
def AgreementSystem.isInverse (sys : AgreementSystem) (ea ia : Person) : Bool :=
  isInverseContext sys.geometry sys.probe ea ia

/-- The external argument is person-licensed by the core probe when some segment Agrees with
it on the second cycle, the Person Licensing Condition of [bejar-rezac-2009]. -/
def eaIsLicensed (geom : Geometry) (probe : Probe.Articulation) (ea ia : Person) : Bool :=
  eaAgrees geom probe ea ia

/-- The external argument is unlicensed exactly in inverse contexts. -/
theorem plc_violation_iff_inverse (geom : Geometry) (probe : Probe.Articulation)
    (ea ia : Person) :
    eaIsLicensed geom probe ea ia = false ↔ isInverseContext geom probe ea ia = true := by
  simp [eaIsLicensed, isInverseContext]

/-- Every context is direct or inverse and not both. -/
theorem direct_inverse_exhaustive (geom : Geometry) (probe : Probe.Articulation)
    (ea ia : Person) :
    (isDirectContext geom probe ea ia = true) ≠ (isInverseContext geom probe ea ia = true) := by
  simp only [isDirectContext, isInverseContext]
  cases eaAgrees geom probe ea ia <;> decide

/-- Arguments of the same person leave the internal argument in control, since the external
argument bears no segment the internal one did not. -/
theorem same_person_ia_controls (geom : Geometry) (probe : Probe.Articulation) (p : Person) :
    agreementController geom probe p p = .ia := by
  simp only [agreementController]
  have h : eaAgrees geom probe p p = false := by
    simp only [eaAgrees]
    suffices ∀ (xs : List Segment) (goal : List Segment),
        ¬ (activeResidue (activeResidue xs goal) goal).length <
          (activeResidue xs goal).length by
      exact Bool.eq_false_iff.mpr (by simpa using this probe (personSpec geom p))
    intro xs goal hlt
    simp only [activeResidue, List.filter_filter] at hlt
    have : ∀ (s : Segment), (!goal.contains s && !goal.contains s) = !goal.contains s := by
      intro s; cases goal.contains s <;> simp
    simp only [this] at hlt
    omega
  rw [h]; rfl

/-- The flat probe leaves no residue. -/
theorem flat_no_residue (geom : Geometry) (ia : Person) :
    activeResidue flatProbe (personSpec geom ia) = [] := by
  cases ia <;> cases geom <;> decide

/-- Under the flat probe the internal argument always controls. -/
theorem flat_ia_controls (geom : Geometry) (ea ia : Person) :
    agreementController geom flatProbe ea ia = .ia := by
  cases ea <;> cases ia <;> cases geom <;> decide

/-- Under the flat probe every context is inverse. -/
theorem flat_all_inverse (geom : Geometry) (ea ia : Person) :
    isInverseContext geom flatProbe ea ia = true := by
  cases ea <;> cases ia <;> cases geom <;> decide

/-- The partial probe behaves alike under the standard and addressee geometries, since
`participant` is geometry-independent. -/
theorem partial_geometry_invariant (ea ia : Person) :
    agreementValue .standard partialProbe ea ia = agreementValue .addressee partialProbe ea ia := by
  cases ea <;> cases ia <;> decide

/-! ### Grounding in relativized search

An articulated probe is a family of flat relativized searches, one per segment, over the
cyclically ordered argument tokens, so cyclic expansion at the level of the whole probe is
first-visible-goal search at the level of each segment. -/

/-- The two arguments as goal tokens in cyclic order, the internal argument first. -/
def goalTokens (ea ia : Person) : List (Controller × Person) :=
  [(.ia, ia), (.ea, ea)]

/-- An argument token is visible to a segment when its person bears the segment. -/
def segVisible (geom : Geometry) (s : Segment) (t : Controller × Person) : Bool :=
  (personSpec geom t.2).contains s

/-- A probe segment as a `Probe` over argument tokens. -/
def segProbe (geom : Geometry) (s : Segment) : Probe (Controller × Person) :=
  .ofVis (segVisible geom s)

/-- The goal a single segment Agrees with, the first argument in cyclic order that bears it. -/
def segmentGoal (geom : Geometry) (ea ia : Person) (s : Segment) :
    Option (Controller × Person) :=
  (segProbe geom s).search (goalTokens ea ia)

/-- A segment finds the external argument iff the internal argument bypasses it and the
external one bears it. -/
theorem segmentGoal_eq_ea_iff (geom : Geometry) (ea ia : Person) (s : Segment) :
    segmentGoal geom ea ia s = some (.ea, ea) ↔
      (personSpec geom ia).contains s = false ∧ (personSpec geom ea).contains s = true := by
  simp only [segmentGoal, segProbe, Probe.ofVis, Probe.search, goalTokens, segVisible, List.find?]
  cases h1 : (personSpec geom ia).contains s <;>
    cases h2 : (personSpec geom ea).contains s <;> simp

/-- A segment finds the internal argument iff it bears the segment. -/
theorem segmentGoal_eq_ia_iff (geom : Geometry) (ea ia : Person) (s : Segment) :
    segmentGoal geom ea ia s = some (.ia, ia) ↔ (personSpec geom ia).contains s = true := by
  simp only [segmentGoal, segProbe, Probe.ofVis, Probe.search, goalTokens, segVisible, List.find?]
  cases h1 : (personSpec geom ia).contains s <;>
    cases h2 : (personSpec geom ea).contains s <;> simp

/-- The external argument Agrees iff some probe segment is bypassed by the internal argument
and borne by the external one. -/
theorem eaAgrees_iff_exists (geom : Geometry) (probe : Probe.Articulation) (ea ia : Person) :
    eaAgrees geom probe ea ia = true ↔
      ∃ s ∈ probe, (personSpec geom ia).contains s = false ∧
        (personSpec geom ea).contains s = true := by
  simp only [eaAgrees, activeResidue, decide_eq_true_eq,
    List.length_filter_lt_length_iff_exists, List.mem_filter]
  constructor
  · rintro ⟨s, ⟨hs, hia⟩, hea⟩
    exact ⟨s, hs, by simpa using hia, by simpa using hea⟩
  · rintro ⟨s, hs, hia, hea⟩
    exact ⟨s, ⟨hs, by simpa using hia⟩, by simpa using hea⟩

/-- The external argument is licensed iff some segment's relativized search over the cyclic
token order licenses its token. -/
theorem eaIsLicensed_iff_segment_licensed (geom : Geometry) (probe : Probe.Articulation)
    (ea ia : Person) :
    eaIsLicensed geom probe ea ia = true ↔
      ∃ s ∈ probe, (segProbe geom s).Licensed (goalTokens ea ia) (.ea, ea) := by
  rw [eaIsLicensed, eaAgrees_iff_exists]
  exact exists_congr fun s => and_congr_right fun _ => (segmentGoal_eq_ea_iff geom ea ia s).symm

/-- A context is inverse iff no segment's search licenses the external argument's token. -/
theorem plc_violation_iff_no_segment_licensed (geom : Geometry) (probe : Probe.Articulation)
    (ea ia : Person) :
    isInverseContext geom probe ea ia = true ↔
      ∀ s ∈ probe, ¬ (segProbe geom s).Licensed (goalTokens ea ia) (.ea, ea) := by
  rw [← plc_violation_iff_inverse, Bool.eq_false_iff, Ne, eaIsLicensed_iff_segment_licensed]
  simp only [not_exists, not_and]

/-- The cycles factor through the search, the first-cycle segments being those whose search
finds the internal argument and the second-cycle segments those whose search finds the external
one. -/
theorem cycleSegments_eq_segmentGoal_filters (geom : Geometry) (probe : Probe.Articulation)
    (ea ia : Person) :
    cycleSegments geom probe ea ia =
      (probe.filter (fun s => segmentGoal geom ea ia s == some (.ia, ia)),
       probe.filter (fun s => segmentGoal geom ea ia s == some (.ea, ea))) := by
  simp only [cycleSegments, activeResidue, List.filter_filter, Prod.mk.injEq]
  refine ⟨?_, ?_⟩
  · exact List.filter_congr fun s _ => by
      rw [Bool.eq_iff_iff, beq_iff_eq, segmentGoal_eq_ia_iff]
  · exact List.filter_congr fun s _ => by
      rw [Bool.eq_iff_iff, beq_iff_eq, segmentGoal_eq_ea_iff]
      cases h1 : (personSpec geom ia).contains s <;>
        cases h2 : (personSpec geom ea).contains s <;> simp_all

end Minimalist.CyclicAgree
