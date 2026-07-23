import Linglib.Studies.Abusch1997
import Linglib.Semantics.Reference.Context.Tower
import Linglib.Semantics.Reference.Context.Shifts
import Linglib.Data.Examples.Schema
import Linglib.Data.Examples.Schlenker2004

/-!
# [schlenker-2004-sot]: Sequence phenomena and double access readings generalized
[schlenker-2004-sot] [schlenker-2003] [kaplan-1989] [von-stechow-2009]

Context-tower formalization of embedded tense in the
[schlenker-2004-sot] chapter (*The Syntax of Time*, Lecarme &
Guéron eds., MIT Press) — the tense-specific application of the
monster-context framework introduced in [schlenker-2003]'s *A Plea
for Monsters*. The core insight: embedded tense is modeled as a
`temporalShift` on a `ContextTower`, and the embedded clause's
perspective time is read from the shifted (innermost) context.
Indexical-rigid expressions read from `.origin` ([kaplan-1989]'s
thesis); shifted expressions read from `.local`.

[klecha-2016] cites the [schlenker-2004-sot] chapter
(not the 2003 *L&P* paper) as the variant of this analysis that "does
not depend on morphosyntactic labels" (PDF p. 33).

## Historical / Narrative Present

Schlenker's CT/CU split is also the semantic-theory anchor for the
**Historical Present** construction (the narrative use of present-
tense morphology to describe past events: "Napoleon enters the
room"; the WWII Vercors example below). The Context of Thought is
shifted into the past so present-tense forms locate the event at the
narrative now; adverbials anchored to the Context of Utterance
("fifty eight years ago to this day") produce the characteristic
"I was there" effect. Sociolinguistic / discourse-analytic accounts
of HP — [wolfson-1979], [schiffrin-1981] — describe when
speakers shift into Conversational Historical Present in oral
narrative and what discourse functions the shift serves; Schlenker's
2004 contribution is the formal-semantic mechanism that makes the
form-meaning mismatch derivable.

The general-indexicals content of [schlenker-2003] lives at
`Studies/Schlenker2003.lean`.

## Derivation Chain

```
Semantics.Context.Tower (ContextTower, push, innermost, origin)
    ↓
Semantics.Context.Shifts (temporalShift: changes time, preserves agent/world)
    ↓
This file: tower operations produce the Reichenbach frames in Studies/Abusch1997.lean
    ↓
Abusch1997 (matrixSaid, embeddedSickSimultaneous, etc.)
```

## Key Results

1. **Root clause = root tower**: `contextAt 0 = origin`, so P = S (speech time)
2. **SOT embedding = temporal shift**: `temporalShift(matrixEventTime)` produces
   the embedded perspective time P' = E_matrix
3. **Double access = origin reading**: present-under-past reads time from `.origin`
   (speech time), not `.local` (matrix event time) — Kaplan's thesis
4. **Tower depth = embedding depth**: one attitude verb = depth 1; nested
   attitudes = depth 2+

-/

open Tense

namespace Schlenker2004

open Semantics.Context
open Abusch1997
open Data.Examples (LinguisticExample)

-- ============================================================================
-- § Tower-Based Tense Model
-- ============================================================================

/-- A minimal tense context: world, agent, position, and time (as ℤ). -/
abbrev TenseCtx := KContext Unit Unit Unit ℤ

/-- The speech-act context: time = 0 (speech time). -/
def speechCtx : TenseCtx :=
  { world := (), agent := (), addressee := (), time := 0, position := () }

-- ============================================================================
-- § Root Clause = Root Tower
-- ============================================================================

/-- A root clause is a tower with no shifts: depth 0. -/
def rootTower : ContextTower TenseCtx := ContextTower.root speechCtx

/-- In a root tower, the innermost context IS the origin.
    Therefore P = S (perspective time = speech time), which is the
    defining property of root clauses in the Reichenbach framework. -/
theorem root_perspective_eq_speech :
    rootTower.innermost.time = rootTower.origin.time := rfl

/-- Root tower has depth 0. -/
theorem root_depth_zero : rootTower.depth = 0 := rfl

-- ============================================================================
-- § SOT Embedding = Temporal Shift
-- ============================================================================

/-- "John said..." pushes a temporal shift: the matrix event time (-2)
    becomes the embedded clause's perspective time.

    This models [von-stechow-2009]: the attitude verb transmits its event
    time to the embedded clause. -/
def sotTower : ContextTower TenseCtx :=
  rootTower.push (temporalShift (-2))

/-- After the temporal shift, the embedded perspective time is the matrix
    event time (-2), not the speech time (0). This is the SOT mechanism:
    embedded tense is evaluated relative to the matrix event time. -/
theorem sot_perspective_shifted :
    sotTower.innermost.time = -2 := rfl

/-- The temporal shift doesn't change the origin — speech time is still 0.
    This is Kaplan's thesis: the speech-act context is invariant under
    embedding. -/
theorem sot_origin_preserved :
    sotTower.origin.time = 0 := rfl

/-- SOT tower has depth 1 (one embedding). -/
theorem sot_depth_one : sotTower.depth = 1 := rfl

/-- The embedded perspective time (-2) equals the matrix event time in
    `matrixSaid`. This is the end-to-end bridge: tower operation →
    Reichenbach frame. -/
theorem sot_perspective_matches_matrix_event :
    sotTower.innermost.time = matrixSaid.eventTime := rfl

/-- The simultaneous reading: embedded R' = embedded P = matrix E = -2.
    This matches `embeddedSickSimultaneous.perspectiveTime`. -/
theorem simultaneous_perspective_match :
    sotTower.innermost.time = embeddedSickSimultaneous.perspectiveTime := rfl

-- ============================================================================
-- § Double Access = Origin Reading
-- ============================================================================

/-- "John said Mary IS sick" (present-under-past): the present tense in the
    embedded clause reads from the ORIGIN (speech time), not from the shifted
    context. This is the double-access reading: the embedded present anchors
    to speech time despite being under a past matrix verb.

    Tower model: the embedded present uses `DepthSpec.origin` for its
    temporal coordinate, reading time = 0 from the origin. -/
def presentAccess : AccessPattern TenseCtx ℤ :=
  { depth := .origin, project := KContext.time }

/-- Present-under-past reads speech time (0), not matrix event time (-2). -/
theorem double_access_reads_speech_time :
    presentAccess.resolve sotTower = 0 := rfl

/-- The embedded present's time (0) matches the speech time in
    `embeddedSickPresent`. End-to-end: tower origin access → Reichenbach
    frame perspective time. -/
theorem double_access_matches_data :
    presentAccess.resolve sotTower = embeddedSickPresent.speechTime := rfl

-- ============================================================================
-- § Shifted Reading = Local Reading
-- ============================================================================

/-- The shifted reading ("Mary WAS sick before John said so") reads from
    the LOCAL (innermost) context. The embedded past tense evaluates its
    reference time relative to the shifted perspective time. -/
def shiftedAccess : AccessPattern TenseCtx ℤ :=
  { depth := .local, project := KContext.time }

/-- Shifted reading reads matrix event time (-2) from the innermost context. -/
theorem shifted_reads_matrix_time :
    shiftedAccess.resolve sotTower = -2 := rfl

/-- The shifted reading's perspective time matches the embedded frame. -/
theorem shifted_matches_data :
    shiftedAccess.resolve sotTower = embeddedSickShifted.perspectiveTime := rfl

-- ============================================================================
-- § Kaplan's Thesis: Origin Stability
-- ============================================================================

/-- Kaplan's thesis formalized: an origin-accessing expression yields the
    same value regardless of how many shifts are pushed. The speech time
    is invariant under SOT embedding. -/
theorem kaplan_thesis_for_tense :
    presentAccess.resolve sotTower = presentAccess.resolve rootTower := by
  exact presentAccess.origin_stable rfl rootTower (temporalShift (-2))

-- ============================================================================
-- § Nested Embedding = Multiple Shifts
-- ============================================================================

/-- "John said that Mary believed that Bill was sick" — double embedding.
    Two temporal shifts: first to John's saying time (-2), then to Mary's
    believing time (-4). -/
def nestedTower : ContextTower TenseCtx :=
  sotTower.push (temporalShift (-4))

/-- Double embedding has depth 2. -/
theorem nested_depth_two : nestedTower.depth = 2 := rfl

/-- The innermost context in a doubly-embedded clause reads the most deeply
    shifted time (-4). -/
theorem nested_innermost :
    nestedTower.innermost.time = -4 := rfl

/-- Even under double embedding, the origin (speech time) is preserved. -/
theorem nested_origin_preserved :
    nestedTower.origin.time = 0 := rfl

/-- Double access still works at depth 2: present-under-past-under-past
    reads from the origin. -/
theorem nested_double_access :
    presentAccess.resolve nestedTower = 0 := by
  exact presentAccess.origin_stable rfl sotTower (temporalShift (-4))

-- ============================================================================
-- § F3. Phase F bridge: Schlenker (origin reading) ↔ Abusch (double access)
-- ============================================================================

/-! [abusch-1997]'s `doubleAccess p speechTime matrixEventTime`
predicate (`p speechTime ∧ p matrixEventTime`, formalized in
`Studies/Abusch1997.lean`) and [schlenker-2004-sot]'s
`presentAccess.depth = .origin` mechanism agree on the speech-time
component of the Double Access Reading: both make embedded present
require truth at speech time.

Schlenker's mechanism reads the time *from* `.origin` (= speech time);
Abusch's mechanism asserts the property holds *at* speech time.
Different conceptual moves, same value-level prediction. The bridge
makes the agreement on the speech-time conjunct kernel-checked. -/

open Abusch1997 in
/-- Phase F bridge — Schlenker-Abusch on the speech-time component of
    Double Access: Schlenker's `.origin` reading discharges the first
    conjunct of [abusch-1997]'s `doubleAccess`. -/
theorem schlenker_origin_supports_abusch_double_access
    (p : ℤ → Prop) (h_speech : p (presentAccess.resolve sotTower))
    (h_matrix : p matrixSaid.eventTime) :
    Tense.doubleAccess p
      (presentAccess.resolve sotTower) matrixSaid.eventTime :=
  ⟨h_speech, h_matrix⟩


-- ============================================================================
-- § Substrate Bridge: Schlenker tower-shifts ↔ Abusch `TimeConcept`s
-- ============================================================================

/-! Substrate-level bridge from [schlenker-2004-sot]'s tower-shift
    framework to [abusch-1997]'s `TimeConcept` substrate
    (`Semantics/Tense/DeRe.lean`). Both formalisms resolve
    against the same `KContext` substrate (= `TenseCtx`); the
    substrate's `Intension.IsRigid` predicate distinguishes
    Kaplan-stable readings (Schlenker's `presentAccess`, origin depth)
    from shifted readings (`shiftedAccess`, local depth).

    [schlenker-2004-sot] (§0, p. 5) explicitly positions the
    SOT chapter as "developing a somewhat generalized version of the
    theory of Abusch 1997, and especially of her Upper Limit
    Constraint." This bridge makes that relationship substrate-level
    structural: both frameworks discriminate Kaplan-stable from
    shifted via `Intension.IsRigid`, and `IsRigid.map` lifts
    the discrimination uniformly across `Res` types — so the
    parallel with [anand-nevins-2004]'s Kaplan-compliant vs
    shifted indexicals at `Res = Agent`
    (`Studies/AnandNevins2004.lean`) is
    substrate-level visible.

    **Caveat on the underlying formalization**: the tower-depth
    framework above is a substantial simplification of
    [schlenker-2004-sot]'s actual SOT mechanism. Per §1.3
    (def. 22), Schlenker's mechanism uses *morphological-agreement
    rules* whose features can be semantically invisible — the
    embedded tense's `<he, past, ind>` triple is transmitted
    morphologically without semantic interpretation in many cases,
    leaving the truth-conditions to come from the embedded context's
    coordinates. The substrate-level discrimination formalized here
    corresponds to the *idealized* case where access depth determines
    the reading directly, suppressing the morphological-agreement
    layer. The DAR analysis Schlenker develops in §2.2 ("Extending
    Abusch's Account: the Generalized Upper Limit Constraint", p. 22+)
    further builds on presupposition-failure conditions in attitude
    contexts (Schlenker eqs. 38, 40) generalizing Abusch's ULC to
    mood; that's also out of scope for the current substrate bridge. -/

open Tense.DeRe (TimeConcept TemporalDeReReading)

/-- [schlenker-2004-sot]'s **`presentAccess` (origin reading)
    as a rigid `TimeConcept`**: the Kaplan-stable origin reading IS
    the constant intension at speech time. Both formalisms encode
    Kaplan's thesis at the substrate level — Schlenker via tower
    `.origin` access, Abusch via `Intension.rigid`. -/
def schlenkerPresent : TimeConcept Unit Unit Unit ℤ :=
  Intensional.Intension.rigid 0

/-- [schlenker-2004-sot]'s **`shiftedAccess` (local reading)
    as a non-rigid `TimeConcept`**: the local-context reading IS the
    time-projection function `(·.time)` — non-rigid because it varies
    with whatever context is plugged in. Substrate-level analog of
    [anand-nevins-2004]'s `shiftedI = (·.agent)`, transposed
    from `Res = Agent` to `Res = ℤ`. -/
def schlenkerShifted : TimeConcept Unit Unit Unit ℤ :=
  fun c => c.time

/-- **Bridge**: `presentAccess.resolve sotTower` IS `schlenkerPresent`
    evaluated at any context. The rigid-concept value is constant —
    both Schlenker's tower `.origin` mechanism and Abusch's
    `Intension.rigid` predict the same value (= speech time). -/
theorem presentAccess_eq_schlenkerPresent (c : TenseCtx) :
    presentAccess.resolve sotTower = schlenkerPresent c := rfl

/-- **Bridge**: `shiftedAccess.resolve sotTower` IS `schlenkerShifted`
    evaluated at the innermost (locally-shifted) context. Both
    Schlenker's tower `.local` mechanism and the substrate's
    `(·.time)` projection predict the same value (= matrix event time). -/
theorem shiftedAccess_eq_schlenkerShifted :
    shiftedAccess.resolve sotTower = schlenkerShifted sotTower.innermost := rfl

/-- **`schlenkerPresent` is rigid** (Kaplan-stable). Substrate-level
    witness for the SOT chapter's origin-access mechanism. -/
theorem schlenkerPresent_isRigid : Intensional.Intension.IsRigid schlenkerPresent :=
  Intensional.Intension.rigid_isRigid _

/-- **`schlenkerShifted` is non-rigid** (the SOT chapter's shifted
    reading varies with context). Discriminating witness: contexts
    with different `.time` fields (speech time 0 vs matrix event
    time −2). -/
theorem schlenkerShifted_not_isRigid : ¬ Intensional.Intension.IsRigid schlenkerShifted := by
  intro h
  have hContradiction : (0 : ℤ) = -2 :=
    h speechCtx { speechCtx with time := -2 }
  exact absurd hContradiction (by decide)


-- ============================================================================
-- § Cross-Framework Agreement (Schlenker ↔ Abusch on simultaneous SOT)
-- ============================================================================

open Abusch1997 in
/-- **Cross-framework value-coincidence on the simultaneous SOT value**:
    [schlenker-2004-sot]'s `shiftedAccess.resolve sotTower` and
    [abusch-1997]'s `abusch_derives_simultaneous_via_binding`
    (applied with `matrixSaid` as the matrix frame) yield the SAME
    value (= `matrixSaid.eventTime = -2`).

    *Caveat*: This is a **value-coincidence**, not a mechanism
    agreement. Both sides equal `matrixSaid.eventTime` by construction
    (Schlenker's `.local` reading IS the matrix event time; Abusch's
    bound-tense IS bound to it). The theorem documents that the two
    frameworks predict the same surface value at the simultaneous SOT
    case — but they do so via *genuinely different* mechanisms
    (Schlenker via context-shift on the tower, Abusch via
    variable-binding on the temporal assignment), and a deeper bridge
    theorem comparing the *paths* through each mechanism would be
    substantively different from this output-coincidence theorem.

    Per [schlenker-2004-sot] §0 p. 5, the value-coincidence on
    basic SOT cases is by design: Schlenker explicitly proposes
    "a somewhat generalized version of the theory of Abusch 1997".
    Genuine divergence between the two would show up in cases (DAR,
    modals, multiple embedding) where Schlenker's morphological-
    agreement apparatus and Abusch's res-movement make different
    predictions — not yet substrate-formalized. -/
theorem schlenker_abusch_agree_on_simultaneous_value
    (tp : TensePronoun)
    (g : TemporalAssignment ℤ) :
    shiftedAccess.resolve sotTower =
    tp.resolve (Tense.updateTemporal g tp.varIndex matrixSaid.eventTime) := by
  show matrixSaid.eventTime = _
  exact (Abusch1997.abusch_derives_simultaneous_via_binding
    tp g matrixSaid).symm


-- ============================================================================
-- § Architectural Alignment (Schlenker ↔ Abusch ↔ Anand-Nevins)
-- ============================================================================

/-- **Architectural alignment via `Intension.IsRigid` functoriality**:
    the substrate's `Intension.IsRigid` predicate distinguishes
    Kaplan-stable from shifted readings uniformly across all three
    frameworks at the substrate level. The same closure lemmas
    (`IsRigid.map`, `IsRigid.precomp`, `IsRigid.of_map_injective`
    from `Semantics/Intensional/Rigidity.lean`) apply uniformly:

    | Framework                  | Kaplan-stable      | Shifted          |
    |----------------------------|--------------------|------------------|
    | [schlenker-2004-sot]  | `schlenkerPresent` | `schlenkerShifted` |
    | [abusch-1997]         | rigid `TimeConcept`| bound `TimeConcept`|
    | [anand-nevins-2004]   | `kaplanI` (Agent)  | `shiftedI` (Agent) |

    All three rows discriminate via `Intension.IsRigid`. By
    `Intension.IsRigid.map`, rigidity transfers across `Res` types
    via any function — so the cross-`Res`-type parallel between
    Schlenker's tower analysis (Res = ℤ), Abusch's res-movement
    (Res = ℤ), and Anand-Nevins's operator-shift (Res = Agent) is
    *structurally one phenomenon* (Kaplan-stable-vs-shifted)
    realized at different `Res` types via different syntactic
    mechanisms.

    The witness here bundles `schlenkerPresent_isRigid` and
    `schlenkerShifted_not_isRigid`; the SAME `Intension.IsRigid`
    predicate proves both at `Res = ℤ`, parallel to how
    `kaplanI_isRigid` and `shiftedI_not_isRigid` prove it at
    `Res = Agent` in `Studies/AnandNevins2004.lean`. -/
theorem schlenker_substrate_aligned_with_isRigid :
    Intensional.Intension.IsRigid schlenkerPresent ∧
    ¬ Intensional.Intension.IsRigid schlenkerShifted :=
  ⟨schlenkerPresent_isRigid, schlenkerShifted_not_isRigid⟩

/-- **`Intension` functoriality applied to Schlenker**: rigidity of
    `schlenkerPresent` transfers across `Res` types via any
    function `g : ℤ → α`, by `Intension.IsRigid.map`. So
    Schlenker's Kaplan-stability is preserved by the substrate's
    functoriality just as [anand-nevins-2004]'s `kaplanI` is —
    both are instances of the same architectural pattern. -/
theorem schlenkerPresent_lifts_rigidly {α : Type*} (g : ℤ → α) :
    Intensional.Intension.IsRigid (fun c : TenseCtx => g (schlenkerPresent c)) :=
  schlenkerPresent_isRigid.map g


end Schlenker2004
