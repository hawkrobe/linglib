import Linglib.Core.Lexical.VerbClass
import Linglib.Theories.Semantics.Verb.EventStructure
import Linglib.Fragments.English.Predicates.Verbal

/-!
# Majid, Boster & Bowerman (2008)
@cite{majid-boster-bowerman-2008}

The cross-linguistic categorization of everyday events: A study of
cutting and breaking. Cognition 109(2), 235–250.

## Core Contributions

28 typologically diverse languages, 61 video clips depicting "cutting
and breaking" events. Correspondence analysis reveals 4 shared
dimensions along which languages categorize these events:

- **Dim 1: Predictability** of the locus of separation (continuous,
  most important). Sharp instruments on yielding objects → predictable
  (= "cutting"); blunt instruments or hands → unpredictable (= "breaking").
  NOTE: This dimension is continuous in the original correspondence analysis;
  our three-valued discretization (high/intermediate/low) is a simplification.
- **Dim 2: Tearing.** Hand-tear of cloth consistently distinguished
  from both cutting and breaking across 10/28 languages.
- **Dim 3: Snap vs smash.** Among low-predictability events:
  snapping (pressure from both ends on 1D rigid object) vs smashing
  (blow from hammer on 3D rigid object).
- **Dim 4: Poke a hole.** Poking a hole in stretched cloth with a twig.

Languages share the dimensionality but vary in how many categories
they carve and where they place boundaries.

## Integration with linglib

The 4 dimensions project onto existing `RootProfile` features:

| Dimension | Projects onto |
|-----------|--------------|
| Dim 1 (predictability) | `instrumentType` × `patientRob` (derived) |
| Dim 2 (tearing) | `resultType == .separation` ∧ `instrumentType == .hands` |
| Dim 3 (snap/smash) | `forceDir` (bidirectional vs omnidirectional) |
| Dim 4 (poke hole) | specific event type |

Bridge theorems connect to `LevinClass` and `MeaningComponents`:
- @cite{levin-1993}'s cut/break distinction (±contact, ±instrumentSpec)
  corresponds to the endpoints of Dimension 1
- @cite{hale-keyser-1987}'s "separation in material integrity" is the
  shared superordinate category that both cut and break belong to

## Design

`SeparationEvent` is a **point** in the same feature space that
`RootProfile` defines **regions** over. A verb is compatible with an
event iff the event's feature values fall within the verb root's ranges.
This captures the many-to-many mapping between events and verbs that
varies across languages.
-/

namespace MajidBosterBowerman2008

open Core.Verbs
open InstrumentType ObjectDimensionality Robustness ResultType
     ForceLevel ForceDirection

-- ════════════════════════════════════════════════════
-- § 1. Separation Events (stimulus level)
-- ════════════════════════════════════════════════════

/-- A separation event characterized by physical properties of the
    action, instrument, and affected object.

    This is the **stimulus level**: each value is a specific point,
    not a range. Corresponds to a single video clip in the experiment.
    Verb roots select *ranges* over these same dimensions
    (via `RootProfile`). -/
structure SeparationEvent where
  /-- Instrument used to effect separation. -/
  instrument : InstrumentType
  /-- Dimensionality of the affected object. -/
  objectDim : ObjectDimensionality
  /-- Material robustness of the affected object. -/
  objectRob : Robustness
  /-- Physical result type. -/
  result : ResultType
  /-- Force magnitude. -/
  force : ForceLevel
  /-- Force directionality. -/
  forceDir : ForceDirection
  /-- Is the separation reversible (can the object be reassembled)? -/
  reversible : Bool
  deriving DecidableEq, Repr

-- ════════════════════════════════════════════════════
-- § 2. Representative Clips
-- ════════════════════════════════════════════════════

/-! Encodings of representative clips from the appendix. Clip numbers
    follow @cite{majid-boster-bowerman-2008} Appendix (pp. 248–249).
    We encode a representative subset spanning all 4 dimensions rather
    than all 61 clips. -/

/-- Clip 9: Slice carrot lengthwise into two pieces with knife.
    High predictability (sharp blade, rigid 1D object). -/
def clip09_sliceCarrot : SeparationEvent :=
  ⟨.sharpBlade, .oneD, .robust, .surfaceBreach, .moderate, .unidirectional, false⟩

/-- Clip 10: Slice carrot crosswise into multiple pieces with knife. -/
def clip10_sliceCarrotCross : SeparationEvent :=
  ⟨.sharpBlade, .oneD, .robust, .surfaceBreach, .moderate, .unidirectional, false⟩

/-- Clip 24: Cut rope in two with scissors.
    High predictability (sharp blade, 1D object). -/
def clip24_cutRope : SeparationEvent :=
  ⟨.sharpBlade, .oneD, .moderate, .surfaceBreach, .moderate, .unidirectional, false⟩

/-- Clip 32: Cut carrot in half crosswise with single karate chop.
    Intermediate predictability (hand, but directed blow). -/
def clip32_karateCarrot : SeparationEvent :=
  ⟨.hands, .oneD, .robust, .fracture, .high, .unidirectional, false⟩

/-- Clip 1: Tear cloth into two pieces by hand.
    Tearing event (Dimension 2). -/
def clip01_tearCloth : SeparationEvent :=
  ⟨.hands, .twoD, .flimsy, .separation, .moderate, .bidirectional, false⟩

/-- Clip 36: Tear cloth about halfway through with two hands. -/
def clip36_tearClothHalf : SeparationEvent :=
  ⟨.hands, .twoD, .flimsy, .separation, .moderate, .bidirectional, false⟩

/-- Clip 19: Snap twig with two hands.
    Snapping event (Dimension 3). -/
def clip19_snapTwig : SeparationEvent :=
  ⟨.hands, .oneD, .moderate, .fracture, .moderate, .bidirectional, false⟩

/-- Clip 57: Snap carrot with two hands. -/
def clip57_snapCarrot : SeparationEvent :=
  ⟨.hands, .oneD, .robust, .fracture, .moderate, .bidirectional, false⟩

/-- Clip 39: Smash flower pot with single hammer blow.
    Smashing event (Dimension 3). -/
def clip39_smashPot : SeparationEvent :=
  ⟨.bluntImpact, .threeD, .robust, .fragmentation, .high, .omnidirectional, false⟩

/-- Clip 40: Smash plate with single hammer blow. -/
def clip40_smashPlate : SeparationEvent :=
  ⟨.bluntImpact, .twoD, .robust, .fragmentation, .high, .omnidirectional, false⟩

/-- Clip 53: Break stick in two with single downward chisel blow.
    A chisel is sharp-edged but used ballistically (single blow), giving
    intermediate predictability — the sharp edge partially constrains the
    locus of separation but the ballistic delivery reduces control. -/
def clip53_breakStick : SeparationEvent :=
  ⟨.sharpBlade, .oneD, .moderate, .fracture, .high, .unidirectional, false⟩

/-- Clip 45: Poke hole in cloth stretched between two tables with a twig.
    Distinguished on Dimension 4. A twig is a pointed implement but not
    a sharp blade — it breaches the material through puncture, not clean
    cutting. -/
def clip45_pokeHole : SeparationEvent :=
  ⟨.none, .twoD, .flimsy, .surfaceBreach, .low, .unidirectional, false⟩

/-- Clip 7: Push chair back from table (reversible separation). -/
def clip07_pushChair : SeparationEvent :=
  ⟨.hands, .threeD, .robust, .deformation, .low, .unidirectional, true⟩

/-- Clip 33: Open a book (reversible separation). -/
def clip33_openBook : SeparationEvent :=
  ⟨.hands, .twoD, .moderate, .deformation, .low, .unidirectional, true⟩

-- ════════════════════════════════════════════════════
-- § 3. Dimension Projections
-- ════════════════════════════════════════════════════

/-- Predictability of the locus of separation (Dimension 1).

    The most important dimension cross-linguistically. Events where the
    agent has precise control over where separation occurs (sharp blade
    on a yielding surface) are "cutting"; events where the locus is
    unpredictable (blow from a hammer, snapping by hand) are "breaking".

    This is a derived property, not a primitive — it emerges from the
    interaction of instrument type, object properties, and manner. -/
inductive Predictability where
  | high          -- sharp blade, controlled contact → "cutting"
  | intermediate  -- karate chop, directed blow → variable
  | low           -- hammer blow, snapping, tearing → "breaking"
  deriving DecidableEq, Repr

/-- Compute predictability from event features.

    Predictability emerges from the interaction of instrument, force, and
    manner — not from instrument alone. A sharp blade used with controlled
    motion yields high predictability, but the same blade used ballistically
    (e.g., a chisel struck with a single blow) yields only intermediate
    predictability. The paper emphasizes that Dimension 1 is continuous and
    "not adequately captured by any single feature." -/
def SeparationEvent.predictability (e : SeparationEvent) : Predictability :=
  match e.instrument with
  | .sharpBlade =>
    match e.force with
    | .high => .intermediate    -- ballistic blow with sharp tool (e.g., chisel strike)
    | _ => .high                -- controlled cutting with sharp tool
  | .bluntImpact => .low
  | .hands =>
    match e.forceDir with
    | .bidirectional => .low     -- tearing/snapping: unpredictable
    | .omnidirectional => .low   -- smashing by hand: unpredictable
    | .unidirectional => .intermediate  -- karate chop: partly predictable
    | .none => .low
  | .none => .low

/-- Break subtypes within the low-predictability cluster (Dimension 3).

    Among events with unpredictable separation, languages further
    distinguish snapping (pressure from both ends breaks a rigid 1D
    object) from smashing (a blow fragments a rigid 3D object). -/
inductive BreakSubtype where
  | snapping   -- bidirectional pressure on 1D rigid object
  | smashing   -- blow from blunt instrument fragments object
  | other      -- other breaking patterns
  deriving DecidableEq, Repr

/-- Classify break subtype for low-predictability events. -/
def SeparationEvent.breakSubtype (e : SeparationEvent) : BreakSubtype :=
  if e.instrument == .hands && e.forceDir == .bidirectional
     && e.objectDim == .oneD then .snapping
  else if e.instrument == .bluntImpact
     && e.result == .fragmentation then .smashing
  else .other

/-- Is this a tearing event? (Dimension 2)
    Tearing = hand separation of a flat flexible object. -/
def SeparationEvent.isTearing (e : SeparationEvent) : Bool :=
  match e.instrument, e.objectDim, e.result, e.forceDir with
  | .hands, .twoD, .separation, .bidirectional => true
  | _, _, _, _ => false

/-- Is this a "cutting and breaking" event (irreversible material
    destruction) as opposed to a reversible separation? (Dimension 1
    of the first correspondence analysis, before restricting to core
    cut/break events.) -/
def SeparationEvent.isMaterialDestruction (e : SeparationEvent) : Bool :=
  !e.reversible

/-- Is this a hole-poking event? (Dimension 4)

    Poking a hole in a flat flexible object — distinguished from
    cutting and breaking because the object is not separated into
    pieces. The paper notes this emerged as a distinct cluster in 5/28
    languages. Our encoding uses `.none` instrument for the twig since
    `InstrumentType` lacks a `.pointed` variant; the diagnostic feature
    is the combination of surface breach + 2D flexible object. -/
def SeparationEvent.isPokingHole (e : SeparationEvent) : Bool :=
  e.result == .surfaceBreach && e.objectDim == .twoD && e.objectRob == .flimsy

-- ════════════════════════════════════════════════════
-- § 4. Compatibility with RootProfile
-- ════════════════════════════════════════════════════

/-- Is a separation event compatible with a verb root's profile?

    An event is compatible iff each of its feature values falls within
    the root's range for that dimension. Unconstrained dimensions
    (range = none) accept any value. -/
def SeparationEvent.compatibleWith (e : SeparationEvent) (r : RootProfile) : Bool :=
  r.forceMag.isCompatible e.force &&
  r.forceDir.isCompatible e.forceDir &&
  r.patientRob.isCompatible e.objectRob &&
  r.resultType.isCompatible e.result &&
  r.instrumentType.isCompatible e.instrument &&
  r.patientDim.isCompatible e.objectDim

-- ════════════════════════════════════════════════════
-- § 5. Dimension Verification
-- ════════════════════════════════════════════════════

/-- Slicing a carrot with a knife has high predictability. -/
theorem sliceCarrot_high_predictability :
    clip09_sliceCarrot.predictability = .high := rfl

/-- Cutting rope with scissors has high predictability. -/
theorem cutRope_high_predictability :
    clip24_cutRope.predictability = .high := rfl

/-- Karate-chopping a carrot has intermediate predictability. -/
theorem karateCarrot_intermediate :
    clip32_karateCarrot.predictability = .intermediate := rfl

/-- Snapping a twig has low predictability. -/
theorem snapTwig_low_predictability :
    clip19_snapTwig.predictability = .low := rfl

/-- Smashing a pot has low predictability. -/
theorem smashPot_low_predictability :
    clip39_smashPot.predictability = .low := rfl

/-- Tearing cloth is classified as tearing (Dimension 2). -/
theorem tearCloth_is_tearing :
    clip01_tearCloth.isTearing = true := rfl

/-- Snapping a twig is not tearing. -/
theorem snapTwig_not_tearing :
    clip19_snapTwig.isTearing = false := rfl

/-- Snapping a twig is classified as snapping (Dimension 3). -/
theorem snapTwig_is_snapping :
    clip19_snapTwig.breakSubtype = .snapping := rfl

/-- Smashing a pot is classified as smashing (Dimension 3). -/
theorem smashPot_is_smashing :
    clip39_smashPot.breakSubtype = .smashing := rfl

/-- Reversible events (push chair, open book) are not material destruction. -/
theorem pushChair_reversible :
    clip07_pushChair.isMaterialDestruction = false := rfl

theorem openBook_reversible :
    clip33_openBook.isMaterialDestruction = false := rfl

/-- Cutting events are material destruction (irreversible). -/
theorem sliceCarrot_irreversible :
    clip09_sliceCarrot.isMaterialDestruction = true := rfl

/-- Poking a hole in cloth is a hole-poking event (Dimension 4). -/
theorem pokeHole_is_poking :
    clip45_pokeHole.isPokingHole = true := rfl

/-- Cutting a carrot is NOT a hole-poking event. -/
theorem sliceCarrot_not_poking :
    clip09_sliceCarrot.isPokingHole = false := rfl

/-! **Consistency checks for paired clips.**
    Clips depicting the same event type with different objects should
    receive the same dimension classifications. -/

/-- Slicing carrot crosswise ≡ lengthwise in predictability. -/
theorem sliceCarrot_cross_consistent :
    clip10_sliceCarrotCross.predictability = clip09_sliceCarrot.predictability := rfl

/-- Tearing cloth halfway ≡ fully in tearing classification. -/
theorem tearClothHalf_consistent :
    clip36_tearClothHalf.isTearing = clip01_tearCloth.isTearing := rfl

/-- Snapping carrot ≡ snapping twig in break subtype. -/
theorem snapCarrot_consistent :
    clip57_snapCarrot.breakSubtype = clip19_snapTwig.breakSubtype := rfl

/-- Smashing plate ≡ smashing pot in break subtype. -/
theorem smashPlate_consistent :
    clip40_smashPlate.breakSubtype = clip39_smashPot.breakSubtype := rfl

-- ════════════════════════════════════════════════════
-- § 6. Cross-Linguistic Verb Categories
-- ════════════════════════════════════════════════════

/-- English cutting-and-breaking verb categories.

    English has 5 basic categories for material destruction events
    (plus *open*, *take apart* for reversible separations):
    *cut*, *break*, *tear*, *snap*, *smash*. -/
inductive EnglishCBVerb where
  | cut    -- high-predictability separation with sharp instrument
  | break_ -- default low-predictability separation
  | tear   -- hand separation of flexible material
  | snap   -- bidirectional pressure breaking rigid 1D object
  | smash  -- blow fragmenting rigid object
  deriving DecidableEq, Repr

/-- English verb assignment for core cutting-and-breaking events. -/
def englishVerb (e : SeparationEvent) : EnglishCBVerb :=
  if e.reversible then .break_  -- simplification; open/take apart not modeled
  else if e.predictability == .high then .cut
  else if e.isTearing then .tear
  else match e.breakSubtype with
    | .snapping => .snap
    | .smashing => .smash
    | .other => .break_

/-- Yélî Dnye (Papuan isolate, Rossel Island) verb categories.

    @cite{majid-boster-bowerman-2008}: Yélî Dnye speakers used only
    3 different verbs for the 61 clips, yet their categorization still
    correlates with the 4 cross-linguistic dimensions. Demonstrates
    that even languages with minimal verb inventories respect the
    shared dimensional structure.

    The paper reports category count (3 verbs) and how they partition
    the stimulus space but does not list the specific verb forms. We
    use abstract labels (`v1`/`v2`/`v3`) for the three categories.

    **Limitation:** The paper reports (p. 242) that the YD verb for
    tearing was *also* used for carrot-cutting events (clips 37, 9)
    that depict separation along the grain. This grouping principle
    (grain-alignment) is not captured by our predictability-based
    model. Our `SeparationEvent` does not encode grain alignment, so
    `yeliDnyeVerb` incorrectly assigns along-the-grain cutting to `v1`
    rather than `v3`. See `yeliDnye_grain_limitation`. -/
inductive YeliDnyeCBVerb where
  | v1   -- cutting events (high predictability, but see limitation above)
  | v2   -- breaking, smashing events (low predictability, impact)
  | v3   -- snapping, tearing, and along-the-grain separation (hand action)
  deriving DecidableEq, Repr

/-- Yélî Dnye verb assignment (approximate, based on reported
    categorization patterns in the correspondence analysis).

    This model uses predictability as the primary split, which
    captures the overall pattern but misses the grain-alignment
    grouping (see `YeliDnyeCBVerb` docstring). -/
def yeliDnyeVerb (e : SeparationEvent) : YeliDnyeCBVerb :=
  if e.predictability == .high then .v1
  else if e.breakSubtype == .snapping || e.isTearing then .v3
  else .v2

/-! **Tzeltal (Mayan)** has the most fine-grained inventory in the sample:
    speakers used 50+ different verbs for the 61 clips (p. 243). Despite
    this extreme specificity, Tzeltal's categorization still correlates
    with the 4 shared dimensions — the dimensions are robust to both
    very coarse (Yélî Dnye, 3 verbs) and very fine (Tzeltal, 50+ verbs)
    inventories. We do not model Tzeltal verb assignment because the paper
    does not provide sufficient data on individual verb-to-clip mappings
    for 50+ verbs. -/

-- ════════════════════════════════════════════════════
-- § 7. Cross-Linguistic Agreement Theorems
-- ════════════════════════════════════════════════════

/-! All three languages agree on the superordinate cut/break boundary
    (Dimension 1): high-predictability events get a "cutting" verb,
    low-predictability events get a "breaking" verb. The languages
    differ in how finely they subdivide the breaking domain. -/

/-- English and Yélî Dnye agree: slicing a carrot is "cutting". -/
theorem slice_is_cutting_EN : englishVerb clip09_sliceCarrot = .cut := rfl
theorem slice_is_cutting_YD : yeliDnyeVerb clip09_sliceCarrot = .v1 := rfl

/-- English and Yélî Dnye agree: smashing a pot is "breaking". -/
theorem smash_is_breaking_EN : englishVerb clip39_smashPot = .smash := rfl
theorem smash_is_breaking_YD : yeliDnyeVerb clip39_smashPot = .v2 := rfl

/-- English distinguishes tearing from breaking; Yélî Dnye groups
    tearing with snapping (both involve hand action). -/
theorem tear_distinct_EN : englishVerb clip01_tearCloth = .tear := rfl
theorem tear_grouped_YD : yeliDnyeVerb clip01_tearCloth = .v3 := rfl

/-- English distinguishes snapping from general breaking. -/
theorem snap_distinct_EN : englishVerb clip19_snapTwig = .snap := rfl

/-- Yélî Dnye groups snapping with tearing (both hand actions). -/
theorem snap_grouped_YD : yeliDnyeVerb clip19_snapTwig = .v3 := rfl

-- ════════════════════════════════════════════════════
-- § 8. Bridge to Levin Classes and MeaningComponents
-- ════════════════════════════════════════════════════

/-- High-predictability events correspond to Levin's *cut* class
    meaning components: change of state + contact + motion + causation
    + instrument specification. -/
theorem cut_cluster_matches_levin_cut :
    MeaningComponents.cut.changeOfState = true
    ∧ MeaningComponents.cut.contact = true
    ∧ MeaningComponents.cut.motion = true
    ∧ MeaningComponents.cut.causation = true
    ∧ MeaningComponents.cut.instrumentSpec = true := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- Low-predictability events correspond to Levin's *break* class:
    change of state + causation, but NO contact, motion, or instrument
    specification. The absence of contact/motion/instrumentSpec reflects
    the fact that break verbs are underspecified for manner — consistent
    with the unpredictability of the separation locus. -/
theorem break_cluster_matches_levin_break :
    MeaningComponents.break_.changeOfState = true
    ∧ MeaningComponents.break_.contact = false
    ∧ MeaningComponents.break_.motion = false
    ∧ MeaningComponents.break_.causation = true
    ∧ MeaningComponents.break_.instrumentSpec = false := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The cut/break distinction in MeaningComponents captures the
    endpoints of Dimension 1: *cut* specifies manner (instrumentSpec,
    contact, motion) while *break* does not. -/
theorem cut_specifies_manner_break_does_not :
    MeaningComponents.cut.instrumentSpec = true
    ∧ MeaningComponents.break_.instrumentSpec = false := ⟨rfl, rfl⟩

/-- Both *cut* and *break* map to accomplishment templates —
    they share event structure ([ACT CAUSE [BECOME ⟨STATE⟩]]) and differ
    only in root content. This explains why the cut/break distinction
    is about manner/predictability (root-level), not about event
    structure (template-level). -/
theorem cut_break_same_template :
    LevinClass.cut.eventTemplate = LevinClass.break_.eventTemplate :=
  rfl

-- ════════════════════════════════════════════════════
-- § 9. Bridge to Fragment Root Profiles
-- ════════════════════════════════════════════════════

/-! Rather than defining inline profiles, we derive them from the actual
    Fragment entries in `Fragments.English.Predicates.Verbal`. This
    ensures that compatibility theorems test the real lexical data. -/

open Fragments.English.Predicates.Verbal in
/-- Extract the root profile from a Fragment verb entry. -/
private def fragmentProfile (v : VerbEntry) : RootProfile :=
  v.rootProfile.getD {}

open Fragments.English.Predicates.Verbal

/-- The tear cloth event is compatible with the Fragment *tear* entry. -/
theorem tearCloth_compatible_tear :
    clip01_tearCloth.compatibleWith (fragmentProfile tear_) = true := rfl

/-- A cutting event is NOT compatible with the *tear* profile
    (wrong instrument type). -/
theorem sliceCarrot_incompatible_tear :
    clip09_sliceCarrot.compatibleWith (fragmentProfile tear_) = false := rfl

/-- Smashing a pot is NOT compatible with the *break* profile
    (fragmentation ≠ fracture — English *smash* covers fragmentation). -/
theorem smashPot_incompatible_break :
    clip39_smashPot.compatibleWith (fragmentProfile break_) = false := rfl

/-- A snapping event IS compatible with *break* (fracture result, moderate
    force) — English *break* can cover snapping events, though *snap*
    is more specific. -/
theorem snapTwig_compatible_break :
    clip19_snapTwig.compatibleWith (fragmentProfile break_) = true := rfl

/-- Slicing a carrot is compatible with the *cut* entry. -/
theorem sliceCarrot_compatible_cut :
    clip09_sliceCarrot.compatibleWith (fragmentProfile cut) = true := rfl

/-- Tearing cloth is NOT compatible with the *cut* profile (wrong instrument). -/
theorem tearCloth_incompatible_cut :
    clip01_tearCloth.compatibleWith (fragmentProfile cut) = false := rfl

-- ════════════════════════════════════════════════════
-- § 10. Key Finding: Dimensional Constraint
-- ════════════════════════════════════════════════════

/-- The 4 dimensions are not independent: tearing events (Dim 2)
    always have low predictability (Dim 1). -/
theorem tearing_implies_low_predictability (e : SeparationEvent)
    (h : e.isTearing = true) :
    e.predictability = .low := by
  obtain ⟨inst, dim, rob, res, f, fd, rev⟩ := e
  simp only [SeparationEvent.isTearing] at h
  cases inst <;> cases dim <;> cases res <;> cases fd <;>
    simp_all [SeparationEvent.predictability]

/-- High-predictability events are never tearing events.
    Contrapositive of: tearing → low predictability. -/
theorem high_predictability_not_tearing (e : SeparationEvent)
    (h : e.predictability = .high) :
    e.isTearing = false := by
  obtain ⟨inst, dim, rob, res, f, fd, rev⟩ := e
  simp only [SeparationEvent.predictability] at h
  cases inst <;> cases f <;> cases fd <;> simp_all [SeparationEvent.isTearing]

/-- The superordinate cut/break distinction (Dimension 1) is exhaustive:
    every event is either high, intermediate, or low predictability. -/
theorem predictability_exhaustive (e : SeparationEvent) :
    e.predictability = .high ∨ e.predictability = .intermediate
    ∨ e.predictability = .low := by
  obtain ⟨inst, dim, rob, res, f, fd, rev⟩ := e
  simp only [SeparationEvent.predictability]
  cases inst <;> simp
  · cases f <;> simp
  · cases fd <;> simp

/-- Dimension 3 (snap/smash) is nested within Dimension 1: the snap vs
    smash distinction only applies to low-predictability events. Events
    with high or intermediate predictability always have breakSubtype
    `.other`. This formalizes the hierarchical structure visible in
    the correspondence analysis (Fig. 4). -/
theorem dim3_nested_in_dim1 (e : SeparationEvent)
    (h : e.breakSubtype ≠ .other) :
    e.predictability = .low := by
  obtain ⟨inst, dim, rob, res, f, fd, rev⟩ := e
  -- After splitting inst × fd, each case either has predictability = .low (rfl)
  -- or breakSubtype = .other definitionally (contradicting h)
  cases inst <;> cases fd <;> first | rfl | exact absurd rfl h

/-- The paradigmatic hole-poking event (clip 45) has low predictability —
    it sits in the "breaking" side of Dimension 1. -/
theorem pokeHole_low_predictability :
    clip45_pokeHole.predictability = .low := rfl

-- ════════════════════════════════════════════════════
-- § 11. Cross-Linguistic Disagreement
-- ════════════════════════════════════════════════════

/-! The key relativity finding: languages share the dimensional structure
    but place category boundaries at different points. English makes finer
    distinctions than Yélî Dnye — and crucially, the languages *disagree*
    on intermediate events. -/

/-- English and Yélî Dnye DISAGREE on tearing: English gives *tear* its
    own category; Yélî Dnye groups it with snapping under a single verb
    (hand-action separation). -/
theorem tear_disagreement :
    englishVerb clip01_tearCloth ≠ englishVerb clip19_snapTwig
    ∧ yeliDnyeVerb clip01_tearCloth = yeliDnyeVerb clip19_snapTwig :=
  ⟨by decide, rfl⟩

/-- English distinguishes smashing from snapping; Yélî Dnye distinguishes
    them too (different verbs). This is an *agreement* on Dimension 3. -/
theorem dim3_agreement :
    englishVerb clip39_smashPot ≠ englishVerb clip19_snapTwig
    ∧ yeliDnyeVerb clip39_smashPot ≠ yeliDnyeVerb clip19_snapTwig :=
  ⟨by decide, by decide⟩

/-- The chisel-blow event (clip 53, intermediate predictability) is a
    boundary case: it has a sharp instrument but ballistic delivery.
    English categorizes it as *break* (the result matters more than the
    instrument for English), while Yélî Dnye's v1 covers all
    high-predictability events. -/
theorem chiselBlow_english_break :
    englishVerb clip53_breakStick = .break_ := rfl

theorem chiselBlow_yeliDnye :
    yeliDnyeVerb clip53_breakStick = .v2 := rfl

/-- **Known limitation of the Yélî Dnye model.**
    Our model assigns clip 9 (slice carrot lengthwise) to v1 (cutting),
    but the paper reports that Yélî Dnye groups this event with tearing
    (v3) — both involve separation along the grain of the material.
    This documents the mismatch: the real YD system uses grain-alignment
    as a grouping principle that our `SeparationEvent` cannot express. -/
theorem yeliDnye_grain_limitation :
    yeliDnyeVerb clip09_sliceCarrot = .v1
    ∧ clip09_sliceCarrot.predictability = .high := ⟨rfl, rfl⟩

end MajidBosterBowerman2008
