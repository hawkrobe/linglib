import Linglib.Syntax.Minimalist.Phi.Geometry
import Linglib.Syntax.Minimalist.Probe.Phi

/-!
# Cyclic Agree [bejar-rezac-2009]

[bejar-rezac-2009] derive person hierarchy (PH) effects from three
independently motivated mechanisms:

1. **Articulated φ-features**: person is decomposed into hierarchical
   *segments* — [π] ⊂ [participant] ⊂ [speaker]/[addressee] — each of
   which can independently enter Agree.
2. **Feature-relativized locality**: a probe segment [uF] only sees goals
   bearing [F]; a goal lacking [F] is bypassed, leaving an *active residue*.
3. **Cyclic expansion**: v's probe first Agrees with the IA (cycle I), then
   with the EA (cycle II). The IA is preferred because cyclicity puts it
   in the search space first.

The interaction of probe articulation and cyclic Agree derives:

- **Agreement displacement**: IA agreement bleeds EA agreement when the
  IA fully checks the probe. When it doesn't, residue reaches the EA.
- **Direct/Inverse contexts**: Inverse = core probe doesn't Agree with EA
  (IA fully checks, or EA can't match the residue). Direct = EA Agrees
  with residue segments.
- **Crosslinguistic variation**: languages differ in probe articulation —
  flat [u-3] (no PH sensitivity), partial [u-3-2] (SAP vs 3P), or
  full [u-3-2-1] (all persons distinguished).

## Person Geometries

Two attested geometries for the innermost feature:

- **Standard (1>2>3)**: [speaker] distinguishes 1st from 2nd. Used by
  Basque, Georgian ([bejar-rezac-2009] Table 2B).
- **Addressee (2>1>3)**: [addressee] distinguishes 2nd from 1st. Used by
  Nishnaabemwin, Mohawk ([bejar-rezac-2009] Table 2C).

## Person Licensing and Repair

The **Person-Licensing Condition** (PLC) requires every π-feature to be
licensed by Agree. In inverse contexts, the EA's π-features are not
licensed by the core probe, triggering **repair strategies**:

- **Added probe**: an extra probe is inserted on v_II in inverse contexts
  (Nishnaabemwin, Mohawk, Basque)
- **R-Case**: the IA receives a special oblique Case (Kashmiri)

Both strategies are derivationally bounded: they occur in all and only
inverse contexts.

## Integration

Connects to `Phi/Geometry.lean` via bridge theorems. The direct/inverse
classification predicts which languages show differential P indexing
(Basque, Georgian fragments).

## Sibling mechanisms in `Syntax/Minimalism/`

`NestedAgree.lean` ([amato-2025]) and Long-Distance Agree
([szabolcsi-2009], `Studies/Allotey2021.lean`) are sibling Layer-2
patterns. All three address what a probe does beyond its first
operation, but differently:

- **Cyclic Agree** (this file): *single articulated probe* with
  multiple feature segments; cycle II's residue probing *expands*
  the domain to reach the EA after the IA partially checks the probe.
- **Nested Agree**: *multiple ordered probes* on one head, all
  forced under maximized matching to target the same goal; each
  subsequent probe operates on a *truncated* domain restricted to
  the first goal's daughters.
- **Long-Distance Agree**: a single probe relaxes clause-locality
  across a non-defective C.

The three are conceptually orthogonal — Cyclic addresses
articulation, Nested addresses ordering, LDA addresses
clause-boundedness. A given construction may instantiate one but
not the others.

-/

namespace Minimalist.CyclicAgree

open Minimalist (DecomposedPerson decomposePerson)

-- ============================================================================
-- § 1: Person Segments
-- ============================================================================

/-- A single segment in an articulated person feature structure.

    Segments are privative features organized in a containment hierarchy.
    Every person value bears [π]; SAPs additionally bear [participant];
    the innermost feature ([speaker] or [addressee]) distinguishes
    1st from 2nd person. -/
inductive Segment where
  | pi          -- [π] — present on all persons
  | participant -- [participant] — present on 1st and 2nd
  | speaker     -- [speaker] — 1st person in standard (1>2>3) geometry
  | addressee   -- [addressee] — 2nd person in addressee (2>1>3) geometry
  deriving DecidableEq, Repr, Inhabited

-- ============================================================================
-- § 2: Person Geometry
-- ============================================================================

/-- Which feature distinguishes 1st from 2nd person.

    - `standard`: [speaker] distinguishes 1st (Basque, Georgian)
    - `addressee`: [addressee] distinguishes 2nd (Nishnaabemwin, Mohawk) -/
inductive Geometry where
  | standard   -- 1>2>3: 1st person most specified
  | addressee  -- 2>1>3: 2nd person most specified
  deriving DecidableEq, Repr

/-- The person specification for a given person value under a geometry.

    Returns the list of segments a DP of this person bears. -/
def personSpec (geom : Geometry) : Person → List Segment
  | .third | .zero => [.pi]
  | .first | .firstInclusive | .firstExclusive => match geom with
    | .standard  => [.pi, .participant, .speaker]
    | .addressee => [.pi, .participant]
  | .second => match geom with
    | .standard  => [.pi, .participant]
    | .addressee => [.pi, .participant, .addressee]

/-- The most specified person under a given geometry. -/
def mostSpecified : Geometry → Person
  | .standard  => .first
  | .addressee => .second

-- ============================================================================
-- § 3: Probe Articulation
-- ============================================================================

/-- An articulated probe: a list of unvalued segments, ordered from
    outermost (most general) to innermost (most specific).

    Languages vary parametrically in probe articulation:
    - Flat [u-3]: no PH sensitivity (e.g., Swahili, Abkhaz)
    - Partial [u-3-2]: distinguishes SAP from 3P (e.g., Basque, Georgian)
    - Full [u-3-2-1]: distinguishes all persons (e.g., Nishnaabemwin, Mohawk) -/
abbrev _root_.Minimalist.Probe.Articulation := List Segment

/-- Flat probe: [uπ]. Any DP fully matches. -/
def flatProbe : Probe.Articulation := [.pi]

/-- Partial probe: [uπ, uParticipant]. Distinguishes SAP from 3P.
    Geometry-independent: [participant] is the same in both geometries. -/
def partialProbe : Probe.Articulation := [.pi, .participant]

/-- Full probe in standard geometry: [uπ, uParticipant, uSpeaker]. -/
def fullProbeStd : Probe.Articulation := [.pi, .participant, .speaker]

/-- Full probe in addressee geometry: [uπ, uParticipant, uAddressee]. -/
def fullProbeAddr : Probe.Articulation := [.pi, .participant, .addressee]

-- ============================================================================
-- § 4: Agreement System (Language Parameterization)
-- ============================================================================

/-- A language's agreement system: the geometry and characteristic probe.

    [bejar-rezac-2009] parameterize crosslinguistic variation by
    two choices: (1) which geometry organizes the innermost feature, and
    (2) how articulated the probe is. The full probe depends on the
    geometry (standard uses [speaker], addressee uses [addressee]). -/
structure AgreementSystem where
  geometry : Geometry
  probe : Probe.Articulation
  deriving DecidableEq, Repr

/-- Swahili/Abkhaz: flat probe, no PH sensitivity. -/
def swahili : AgreementSystem := ⟨.standard, flatProbe⟩

/-- Basque/Georgian: partial probe, standard geometry. -/
def basque : AgreementSystem := ⟨.standard, partialProbe⟩

/-- Nishnaabemwin/Mohawk: full probe, addressee geometry. -/
def nishnaabemwin : AgreementSystem := ⟨.addressee, fullProbeAddr⟩

-- ============================================================================
-- § 5: Active Residue
-- ============================================================================

/-- Active residue: unmatched probe segments after Agree with a goal DP.

    Each probe segment that has a corresponding segment in the goal's
    person specification is *deactivated* (matched). Segments without
    a match remain *active* and can participate in further Agree on
    the next cycle.

    This is the core operation of [bejar-rezac-2009]: partial
    matching of articulated probes drives agreement displacement. -/
def activeResidue (probe : Probe.Articulation) (goal : List Segment) : Probe.Articulation :=
  probe.filter (fun s => !goal.contains s)

-- ============================================================================
-- § 6: Cyclic Agree — Controller and Cycle Information
-- ============================================================================

/-- Which argument controls the core agreement slot. -/
inductive Controller where
  | ia   -- Internal argument controls (inverse context)
  | ea   -- External argument controls (direct context)
  deriving DecidableEq, Repr

/-- Does the EA Agree with residue segments on cycle II?

    Returns `true` iff the EA matches at least one segment that the
    IA left unmatched. -/
def eaAgrees (geom : Geometry) (probe : Probe.Articulation)
    (ea ia : Person) : Bool :=
  let residue := activeResidue probe (personSpec geom ia)
  let residueAfterEA := activeResidue residue (personSpec geom ea)
  residueAfterEA.length < residue.length

/-- Determine which argument controls the core agreement slot.

    Cycle I: probe Agrees with IA. If residue remains, cycle II:
    probe Agrees with EA. EA controls iff it matches any residue
    segment; otherwise IA controls (either it fully checked the
    probe, or it left residue the EA couldn't match). -/
def agreementController (geom : Geometry) (probe : Probe.Articulation)
    (ea ia : Person) : Controller :=
  if eaAgrees geom probe ea ia then .ea else .ia

/-- The person value that the core agreement slot realizes. -/
def agreementValue (geom : Geometry) (probe : Probe.Articulation)
    (ea ia : Person) : Person :=
  match agreementController geom probe ea ia with
  | .ea => ea
  | .ia => ia

/-- Convenience: controller using an `AgreementSystem`. -/
def AgreementSystem.controller (sys : AgreementSystem)
    (ea ia : Person) : Controller :=
  agreementController sys.geometry sys.probe ea ia

/-- Convenience: agreement value using an `AgreementSystem`. -/
def AgreementSystem.value (sys : AgreementSystem)
    (ea ia : Person) : Person :=
  agreementValue sys.geometry sys.probe ea ia

-- ============================================================================
-- § 7: Second-Cycle Effects
-- ============================================================================

/-- Which cycle valued the probe's remaining segments.

    [bejar-rezac-2009] §3.2: when the probe is valued on two
    different cycles, the morphological realization can differ. Georgian
    uses *m-* (first cycle) vs *v-* (second cycle) for 1sg agreement;
    Nishnaabemwin uses *-in* (1P, cycle II) vs *-igw* (3P, cycle II)
    vs *-aa* (default/cycle I only).

    Returns `(cycleI, cycleII)` — the segments deactivated on each cycle. -/
def cycleSegments (geom : Geometry) (probe : Probe.Articulation)
    (ea ia : Person) : Probe.Articulation × Probe.Articulation :=
  let iaSpec := personSpec geom ia
  let cycleI := probe.filter (fun s => iaSpec.contains s)
  let residue := activeResidue probe iaSpec
  let eaSpec := personSpec geom ea
  let cycleII := residue.filter (fun s => eaSpec.contains s)
  (cycleI, cycleII)

/-- Was the probe valued on two distinct cycles?

    True when both the IA (cycle I) and EA (cycle II) matched at least
    one segment. This is the configuration that creates second-cycle
    morphological effects in languages like Georgian and Nishnaabemwin. -/
def hasSecondCycleEffect (geom : Geometry) (probe : Probe.Articulation)
    (ea ia : Person) : Bool :=
  let (c1, c2) := cycleSegments geom probe ea ia
  !c1.isEmpty && !c2.isEmpty

-- ============================================================================
-- § 8: Direct/Inverse Classification
-- ============================================================================

/-- Inverse context: the core π-probe on v does NOT Agree with the EA.

    This occurs when either (a) the IA fully checks the probe, leaving
    no residue, or (b) residue exists but the EA cannot match any of it.
    Inverse contexts trigger PLC violations on the EA's π-features,
    requiring repair strategies (added probe or R-Case). -/
def isInverseContext (geom : Geometry) (probe : Probe.Articulation)
    (ea ia : Person) : Bool :=
  !eaAgrees geom probe ea ia

/-- Direct context: the EA Agrees with at least one residue segment. -/
def isDirectContext (geom : Geometry) (probe : Probe.Articulation)
    (ea ia : Person) : Bool :=
  eaAgrees geom probe ea ia

/-- Convenience: inverse using an `AgreementSystem`. -/
def AgreementSystem.isInverse (sys : AgreementSystem)
    (ea ia : Person) : Bool :=
  isInverseContext sys.geometry sys.probe ea ia

-- ============================================================================
-- § 9: Person-Licensing Condition (PLC)
-- ============================================================================

/-- The Person-Licensing Condition (PLC).

    [bejar-rezac-2009] eq. (13): "A π-feature [F] must be licensed
    by Agree of some segment in a feature structure of which [F] is a
    subset."

    In inverse contexts, the EA's π-features are not licensed by the
    core probe (because the probe either has no residue or residue the
    EA can't match). This drives repair strategies.

    Returns `true` if the EA is person-licensed (its π-features were
    checked by the core probe on cycle II). -/
def eaIsLicensed (geom : Geometry) (probe : Probe.Articulation)
    (ea ia : Person) : Bool :=
  eaAgrees geom probe ea ia

/-- PLC violation: EA is NOT person-licensed. Exactly characterizes
    inverse contexts — this is the paper's key insight connecting
    syntactic derivation to morphological repair. -/
theorem plc_violation_iff_inverse (geom : Geometry) (probe : Probe.Articulation)
    (ea ia : Person) :
    eaIsLicensed geom probe ea ia = false ↔
    isInverseContext geom probe ea ia = true := by
  simp [eaIsLicensed, isInverseContext]

/-! ### Grounding in relativized search (`Probe/Basic.lean`)

An articulated probe is a *family* of flat relativized searches, one
per segment, over the cyclically ordered token list: B&R's segments
match independently, so cyclic expansion at the whole-probe level is
first-visible-goal search at the per-segment level. The residue-based
definitions above remain definitional — they are the paper's
mechanism; the factorization is a *result* about it.

Cf. `Studies/BejarRezac2003.lean` for the 2003 precursor's
second-cycle repair: formally distinct mechanisms — 2003 varies the
goal *order* under one probe; cyclic expansion here varies the
*relativization* (per segment) over one order. -/

/-- The two arguments as φ-bearing goal tokens, in cyclic search order:
    the IA precedes the EA (cycle I before cycle II). -/
def goalTokens (ea ia : Person) : List (Controller × Person) :=
  [(.ia, ia), (.ea, ea)]

/-- Visibility of an argument token to a probe segment `s`: the
    argument's person specification bears `s` (feature-relativized
    locality). -/
def segVisible (geom : Geometry) (s : Segment) (t : Controller × Person) : Bool :=
  (personSpec geom t.2).contains s

/-- A probe segment as a `Probe` over argument tokens. -/
def segProbe (geom : Geometry) (s : Segment) : Probe (Controller × Person) :=
  .ofVis (segVisible geom s)

/-- The goal a single probe segment Agrees with: the first argument in
    cyclic order whose specification bears the segment — a flat
    relativized `Probe.search`. -/
def segmentGoal (geom : Geometry) (ea ia : Person) (s : Segment) :
    Option (Controller × Person) :=
  (segProbe geom s).search (goalTokens ea ia)

/-- A segment finds the EA token iff the IA bypasses it (leaving it as
    active residue) and the EA bears it — cycle-II Agree. -/
theorem segmentGoal_eq_ea_iff (geom : Geometry) (ea ia : Person) (s : Segment) :
    segmentGoal geom ea ia s = some (.ea, ea) ↔
      (personSpec geom ia).contains s = false ∧
      (personSpec geom ea).contains s = true := by
  simp only [segmentGoal, segProbe, Probe.ofVis, Probe.search, goalTokens, segVisible, List.find?]
  cases h1 : (personSpec geom ia).contains s <;>
    cases h2 : (personSpec geom ea).contains s <;> simp

/-- A segment finds the IA token iff the IA bears it — cycle-I Agree. -/
theorem segmentGoal_eq_ia_iff (geom : Geometry) (ea ia : Person) (s : Segment) :
    segmentGoal geom ea ia s = some (.ia, ia) ↔
      (personSpec geom ia).contains s = true := by
  simp only [segmentGoal, segProbe, Probe.ofVis, Probe.search, goalTokens, segVisible, List.find?]
  cases h1 : (personSpec geom ia).contains s <;>
    cases h2 : (personSpec geom ea).contains s <;> simp

/-- Existential characterization of the residue-based `eaAgrees`. -/
theorem eaAgrees_iff_exists (geom : Geometry) (probe : Probe.Articulation)
    (ea ia : Person) :
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

/-- **Main bridge**: the EA is person-licensed (`eaIsLicensed`) iff some
    probe segment's flat relativized search (`Probe.Licensed`) over
    the cyclically ordered token list finds the EA token. -/
theorem eaIsLicensed_iff_segment_licensed (geom : Geometry)
    (probe : Probe.Articulation) (ea ia : Person) :
    eaIsLicensed geom probe ea ia = true ↔
      ∃ s ∈ probe, (segProbe geom s).Licensed (goalTokens ea ia) (.ea, ea) := by
  rw [eaIsLicensed, eaAgrees_iff_exists]
  exact exists_congr fun s => and_congr_right fun _ =>
    (segmentGoal_eq_ea_iff geom ea ia s).symm

/-- PLC violation ↔ no segment's search licenses the EA token — the
    inverse-context characterization restated through the search
    substrate. -/
theorem plc_violation_iff_no_segment_licensed (geom : Geometry)
    (probe : Probe.Articulation) (ea ia : Person) :
    isInverseContext geom probe ea ia = true ↔
      ∀ s ∈ probe, ¬ (segProbe geom s).Licensed (goalTokens ea ia) (.ea, ea) := by
  rw [← plc_violation_iff_inverse, Bool.eq_false_iff, Ne,
    eaIsLicensed_iff_segment_licensed]
  simp only [not_exists, not_and]

/-- Cycle decomposition through the search: cycle-I segments are those
    whose search finds the IA token; cycle-II segments those whose
    search finds the EA token. Second-cycle effects also factor through
    `Probe.search`. -/
theorem cycleSegments_eq_segmentGoal_filters (geom : Geometry)
    (probe : Probe.Articulation) (ea ia : Person) :
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

-- ============================================================================
-- § 10: Repair Strategies
-- ============================================================================

/-- Repair strategies for PLC violations in inverse contexts.

    [bejar-rezac-2009] §4 identifies two strategies:
    - `addedProbe`: an extra probe is inserted on v_II, creating an
      additional agreement slot for the EA (Nishnaabemwin, Mohawk, Basque)
    - `rCase`: the IA receives a special oblique Case distinct from the
      regular v-assigned Case (Kashmiri) -/
inductive RepairStrategy where
  | addedProbe  -- Extra agreement morphology for EA
  | rCase       -- Special Case on IA in inverse contexts
  deriving DecidableEq, Repr

/-- Does a given EA→IA combination require repair under this system?

    Repair is needed iff the context is inverse. -/
def needsRepair (sys : AgreementSystem) (ea ia : Person) : Bool :=
  sys.isInverse ea ia

-- ============================================================================
-- § 11: Bridge to DecomposedPerson
-- ============================================================================

/-- In the standard geometry, a person value has [participant] as a segment
    iff `DecomposedPerson.hasParticipant` is true. -/
theorem std_participant_matches_decomposed (p : Person) :
    (personSpec .standard p).contains .participant =
    (decomposePerson p).hasParticipant := by
  cases p <;> decide

/-- In the standard geometry, 3rd person has exactly one segment ([π]). -/
theorem std_third_singleton :
    personSpec .standard .third = [.pi] := rfl

/-- Segment count reflects the person hierarchy:
    1st (3 segments) > 2nd (2) > 3rd (1) in standard geometry. -/
theorem std_spec_lengths :
    (personSpec .standard .first).length = 3 ∧
    (personSpec .standard .second).length = 2 ∧
    (personSpec .standard .third).length = 1 := ⟨rfl, rfl, rfl⟩

/-- Entailment: more specified persons' segments are supersets. -/
theorem std_first_entails_second :
    ∀ s ∈ personSpec .standard .second, s ∈ personSpec .standard .first := by
  intro s hs; simp only [personSpec, List.mem_cons, List.mem_nil_iff] at hs ⊢
  rcases hs with rfl | rfl | h <;> simp_all

theorem std_second_entails_third :
    ∀ s ∈ personSpec .standard .third, s ∈ personSpec .standard .second := by
  intro s hs; simp only [personSpec, List.mem_cons, List.mem_nil_iff] at hs ⊢
  rcases hs with rfl | h <;> simp_all

-- ============================================================================
-- § 12: Verification — Flat Probe (no PH sensitivity)
-- ============================================================================

/-- Flat probe: IA always fully checks the probe, regardless of person. -/
theorem flat_no_residue (geom : Geometry) (ia : Person) :
    activeResidue flatProbe (personSpec geom ia) = [] := by
  cases ia <;> cases geom <;> decide

/-- Flat probe: IA always controls — no PH effects. -/
theorem flat_ia_controls (geom : Geometry) (ea ia : Person) :
    agreementController geom flatProbe ea ia = .ia := by
  cases ea <;> cases ia <;> cases geom <;> decide

/-- Flat probe: all contexts are inverse (no EA agreement). -/
theorem flat_all_inverse (geom : Geometry) (ea ia : Person) :
    isInverseContext geom flatProbe ea ia = true := by
  cases ea <;> cases ia <;> cases geom <;> decide

-- ============================================================================
-- § 13: Verification — Partial Probe (Basque/Georgian-type)
-- ============================================================================

section PartialProbe

/-- Partial probe: same behavior in both geometries, since [participant]
    is geometry-independent. -/
theorem partial_geometry_invariant (ea ia : Person) :
    agreementValue .standard partialProbe ea ia =
    agreementValue .addressee partialProbe ea ia := by
  cases ea <;> cases ia <;> decide

/-- Basque: 3→1 = 1 (IA controls, inverse). -/
theorem basque_3_1 : basque.value .third .first = .first := by decide
/-- Basque: 2→1 = 1 (IA controls, inverse). -/
theorem basque_2_1 : basque.value .second .first = .first := by decide
/-- Basque: 1→2 = 2 (IA controls, inverse). -/
theorem basque_1_2 : basque.value .first .second = .second := by decide
/-- Basque: 3→2 = 2 (IA controls, inverse). -/
theorem basque_3_2 : basque.value .third .second = .second := by decide
/-- Basque: 1→3 = 1 (EA controls, direct). -/
theorem basque_1_3 : basque.value .first .third = .first := by decide
/-- Basque: 2→3 = 2 (EA controls, direct). -/
theorem basque_2_3 : basque.value .second .third = .second := by decide
/-- Basque: 3→3 = 3 (IA controls, inverse — residue [uParticipant]
    unmatched by either argument). -/
theorem basque_3_3 : basque.value .third .third = .third := by decide

/-- Basque: SAP IA → inverse context (agreement displacement to IA). -/
theorem basque_sap_ia_inverse (ea : Person) :
    basque.isInverse ea .first = true ∧
    basque.isInverse ea .second = true := by
  constructor <;> cases ea <;> decide

/-- Basque: 3P IA + SAP EA → direct context (EA controls). -/
theorem basque_3p_ia_direct (ea : Person) (h : ea.IsSAP) :
    isDirectContext .standard partialProbe ea .third = true := by
  cases ea <;> simp_all [Person.IsSAP] <;> decide

/-- Basque: 3P IA + 3P EA → inverse (neither fully checks). -/
theorem basque_3_3_inverse : basque.isInverse .third .third = true := by
  decide

end PartialProbe

-- ============================================================================
-- § 14: Verification — Full Probe, Addressee Geometry (Nishnaabemwin-type)
-- ============================================================================

section FullProbeAddr

/-- Nishnaabemwin: 3→2 = 2 (IA controls, inverse — IA fully checks). -/
theorem nish_3_2 : nishnaabemwin.value .third .second = .second := by decide
/-- Nishnaabemwin: 1→2 = 2 (IA controls, inverse — IA fully checks). -/
theorem nish_1_2 : nishnaabemwin.value .first .second = .second := by decide
/-- Nishnaabemwin: 3→1 = 1 (IA controls, inverse — EA can't match residue). -/
theorem nish_3_1 : nishnaabemwin.value .third .first = .first := by decide
/-- Nishnaabemwin: 2→1 = 2 (EA controls, direct — EA matches [uAddressee]). -/
theorem nish_2_1 : nishnaabemwin.value .second .first = .second := by decide
/-- Nishnaabemwin: 1→3 = 1 (EA controls, direct). -/
theorem nish_1_3 : nishnaabemwin.value .first .third = .first := by decide
/-- Nishnaabemwin: 2→3 = 2 (EA controls, direct). -/
theorem nish_2_3 : nishnaabemwin.value .second .third = .second := by decide
/-- Nishnaabemwin: 3→3 = 3 (IA controls, inverse — residue [uParticipant,
    uAddressee] unmatched by 3P EA). -/
theorem nish_3_3 : nishnaabemwin.value .third .third = .third := by decide

/-- Nishnaabemwin: 2P IA → always inverse (2nd is most specified). -/
theorem nish_2p_ia_inverse (ea : Person) :
    nishnaabemwin.isInverse ea .second = true := by
  cases ea <;> decide

/-- Nishnaabemwin: 3P IA with SAP EA → direct. -/
theorem nish_3p_ia_sap_ea_direct :
    isDirectContext .addressee fullProbeAddr .first .third = true ∧
    isDirectContext .addressee fullProbeAddr .second .third = true := by
  constructor <;> decide

/-- Nishnaabemwin: 3→1 is inverse despite residue, because EA (3P) can't
    match [addressee]. -/
theorem nish_3_1_inverse : nishnaabemwin.isInverse .third .first = true := by
  decide

/-- Nishnaabemwin: 3→3 is inverse. -/
theorem nish_3_3_inverse : nishnaabemwin.isInverse .third .third = true := by
  decide

end FullProbeAddr

-- ============================================================================
-- § 15: Second-Cycle Effect Verification
-- ============================================================================

/-- Georgian second-cycle effect: 1sg agreement is *m-* when valued on
    cycle I (IA=1, any EA), but *v-* when valued on cycle II (EA=1, IA=3). -/
theorem georgian_1_3_second_cycle :
    hasSecondCycleEffect .standard partialProbe .first .third = true := by
  decide

/-- Georgian: when IA is SAP, no second cycle (IA fully checks). -/
theorem georgian_no_second_cycle_sap_ia (ea : Person) :
    hasSecondCycleEffect .standard partialProbe ea .first = false ∧
    hasSecondCycleEffect .standard partialProbe ea .second = false := by
  constructor <;> cases ea <;> decide

/-- Nishnaabemwin: 2→1 has a second-cycle effect (IA checks [π,participant],
    EA checks [addressee] on cycle II). -/
theorem nish_2_1_second_cycle :
    hasSecondCycleEffect .addressee fullProbeAddr .second .first = true := by
  decide

/-- Nishnaabemwin: the second cycle in 2→1 values exactly [addressee]. -/
theorem nish_2_1_cycle_segments :
    (cycleSegments .addressee fullProbeAddr .second .first).2 = [.addressee] := by
  decide

-- ============================================================================
-- § 16: General Properties
-- ============================================================================

/-- When EA and IA have the same person, IA always controls (the EA
    contributes nothing new — every segment it could match was already
    matched by the identical IA).

    The proof proceeds by showing that `activeResidue` is idempotent
    when applied with the same goal: if some segments survive matching
    against personSpec(p), applying the same filter again removes nothing,
    so `eaAgrees` returns false. -/
theorem same_person_ia_controls (geom : Geometry) (probe : Probe.Articulation)
    (p : Person) :
    agreementController geom probe p p = .ia := by
  simp only [agreementController]
  -- eaAgrees returns Bool; show it's false so `if` takes else branch
  have h : eaAgrees geom probe p p = false := by
    simp only [eaAgrees]
    -- residue filtered by the same goal twice = filtered once (idempotent)
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

/-- The most specified person always controls against 3P (standard). -/
theorem most_specified_controls_vs_third_std :
    agreementValue .standard fullProbeStd (mostSpecified .standard) .third =
      mostSpecified .standard ∧
    agreementValue .standard fullProbeStd .third (mostSpecified .standard) =
      mostSpecified .standard := by
  constructor <;> decide

/-- The most specified person always controls against 3P (addressee). -/
theorem most_specified_controls_vs_third_addr :
    agreementValue .addressee fullProbeAddr (mostSpecified .addressee) .third =
      mostSpecified .addressee ∧
    agreementValue .addressee fullProbeAddr .third (mostSpecified .addressee) =
      mostSpecified .addressee := by
  constructor <;> decide

/-- The direct/inverse split exhaustively partitions the paradigm:
    every EA→IA combination is either direct or inverse, never both. -/
theorem direct_inverse_exhaustive (geom : Geometry) (probe : Probe.Articulation)
    (ea ia : Person) :
    (isDirectContext geom probe ea ia = true) ≠
    (isInverseContext geom probe ea ia = true) := by
  simp only [isDirectContext, isInverseContext]
  cases eaAgrees geom probe ea ia <;> decide

-- ============================================================================
-- § 17: Bridge to Fragment Data — Differential P Indexing
-- ============================================================================

/-- In a partial-probe language like Basque/Georgian, object (P) agreement
    is person-conditioned: the object controls agreement iff the context
    is direct (EA > IA on the person hierarchy). This predicts that SAP
    objects trigger agreement displacement to EA, while 3P objects don't.

    Formally: for a fixed 3P EA (the "subject" in a canonical transitive),
    a SAP IA triggers direct context (EA controls → "no P indexing"),
    but this is backwards from the traditional description. Let's think
    about it from the P indexing perspective:

    In Basque, the agreement slot tracks the *controller*. When IA is SAP,
    IA controls (inverse) — the agreement tracks IA, reflecting the
    *object*. When IA is 3P, EA controls (direct) — agreement tracks EA,
    not the object.

    So `pIsIndexed` ↔ the IA controls (the agreement slot shows the
    object's features) ↔ inverse context. -/
theorem partial_probe_sap_ia_is_inverse (ea : Person) :
    isInverseContext .standard partialProbe ea .first = true ∧
    isInverseContext .standard partialProbe ea .second = true := by
  constructor <;> cases ea <;> decide

/-- 3P IA yields direct context when EA is SAP — the agreement slot
    tracks the EA, not the (3P) object. -/
theorem partial_probe_3p_ia_sap_ea_is_direct :
    isDirectContext .standard partialProbe .first .third = true ∧
    isDirectContext .standard partialProbe .second .third = true := by
  constructor <;> decide

/-- Differential P indexing prediction: the SAP/3P split in object
    agreement (Basque `pIsIndexed`, Georgian `pIsIndexed`) is exactly
    the inverse/direct split of the partial probe.

    An object (IA) is "indexed" when the core agreement slot tracks
    the IA's person features, which happens iff the context is inverse
    (IA controls). SAP IAs always produce inverse contexts; 3P IAs
    produce direct contexts (when EA is SAP).

    This theorem proves the key direction: SAP IA → inverse (indexed). -/
theorem sap_ia_indexed_via_inverse (p : Person) (h : p.IsSAP) :
    ∀ ea : Person,
      isInverseContext .standard partialProbe ea p = true := by
  intro ea; cases p <;> cases ea <;> simp_all [Person.IsSAP] <;> decide

-- ============================================================================
-- § 18: Inverse Context Counts
-- ============================================================================

/-- Count inverse contexts in a 3×3 paradigm. -/
def inverseCount (sys : AgreementSystem) : Nat :=
  let ps : List Person := [.first, .second, .third]
  (ps.flatMap (λ ea => ps.filter (λ ia => sys.isInverse ea ia))).length

/-- Swahili (flat): all 9 cells are inverse (no PH sensitivity). -/
theorem swahili_all_inverse : inverseCount swahili = 9 := by decide

/-- Basque (partial): 7 inverse, 2 direct (only SAP EA + 3P IA). -/
theorem basque_inverse_count : inverseCount basque = 7 := by decide

/-- Nishnaabemwin (full): 6 inverse, 3 direct. -/
theorem nish_inverse_count : inverseCount nishnaabemwin = 6 := by decide

/-- More articulated probes yield more direct contexts. -/
theorem articulation_increases_direct :
    inverseCount swahili ≥ inverseCount basque ∧
    inverseCount basque ≥ inverseCount nishnaabemwin := by
  constructor <;> decide

end Minimalist.CyclicAgree
