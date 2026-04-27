import Linglib.Theories.Semantics.Verb.DegreeAchievement
import Linglib.Theories.Semantics.Degree.MeasureFunction
import Linglib.Core.Scales.Scale
import Linglib.Fragments.English.Predicates.Verbal

/-!
# @cite{hay-kennedy-levin-1999}: Scalar Structure Underlies Telicity in DAs
@cite{hay-kennedy-levin-1999}

HKL 1999's central claim (p.3): *"when the scalar structure associated
with the base adjective has a natural bound, the derived verb is telic;
when the adjective's scalar structure has no such bound, the verb is
atelic."*

The thesis applies specifically to **degree achievements** (verbs derived
from gradable adjectives — *lengthen, cool, straighten*). The mechanism is
the **INCREASE** function (eq 16), whose **difference value** drives
telicity: bounded difference → telic; unbounded difference → atelic.

## Sections

- §1 — HKL's `INCREASE` operator (eq 16) + bridge note to K&L 2008's
  `measureOfChange` substrate (`Theories/Semantics/Degree/MeasureFunction.lean`).
- §2 — Central matrix prediction (HKL §3.2): closed-range adjective →
  telic DA verb; open-range adjective → atelic DA verb. Verified against
  fragment `degreeAchievementScale` annotations on *straighten* (closed →
  accomplishment) vs *lengthen, widen, cool, warm* (open → activity).
- §3 — Specifying the difference value (HKL §3.1): measure phrases,
  *completely*, *significantly*/*slightly* data.
- §4 — Context-dependent telicity (HKL §3.3): defeasibility-via-implicature
  data.
- §5 — Beyond DAs (HKL §4.1): brief connection to consumption / motion /
  creation that the analysis extends to.

## Relation to KennedyLevin2008.lean

K&L 2008 is the mature successor of HKL 1999. The K&L `measureOfChange`
function (eq 25, in `MeasureFunction.lean`) refines HKL's INCREASE with
explicit clamping at the initial degree (`differenceFunction`, K&L eq 23).
Per-verb derivation of `vendlerClass` from
`degreeAchievementScale.scaleBoundedness` is in
`Phenomena/TenseAspect/Studies/KennedyLevin2008.lean`. This file focuses
on what's specific to HKL 1999: the original INCREASE operator, the §3
data, and the closed/open-range vocabulary HKL introduced (the same
distinction Kennedy & McNally 2005 later canonicalized as
"closed scale"/"open scale").

## Anchoring discipline

§7 of `Phenomena/TenseAspect/Studies/Krifka1989.lean` (added in 0.230.429)
explicitly cites HKL 1999 as the source of the *defeasible*
closed-scale → telic-verb bridge for **degree achievements specifically**.
This file makes that bridge a Lean-checkable matrix on fragment data
rather than docstring prose.
-/

namespace HayKennedyLevin1999

open Core.Scale (Boundedness)
open Fragments.English.Predicates.Verbal

-- ════════════════════════════════════════════════════
-- § 1. HKL's INCREASE operator (eq 16)
-- ════════════════════════════════════════════════════

/-- HKL eq 11: `[long(x)(t)] = the degree to which x is long at time t`.
    A gradable adjective denotes a time-indexed measure function — the
    same shape as K&L 2008's `MeasureFunction α δ Time` in
    `Theories/Semantics/Degree/MeasureFunction.lean`. -/
abbrev TimedAdjective (α δ Time : Type*) := α → Time → δ

/-- HKL eq 16, the INCREASE function:
    `INCREASE(φ)(x)(d)(e) = 1 iff φ(x)(SPO(e)) + d = φ(x)(EPO(e))`.

    True iff `x`'s degree at the end of an event equals its degree at the
    start plus `d`. The "difference value" `d` is HKL's central object;
    its boundedness drives telicity (HKL §3 thesis).

    K&L 2008 reformulates this as a measure-valued function
    `measureOfChange m x initT finT : δ` with explicit
    `differenceFunction` clamping at the initial degree (K&L eq 23).
    The two coincide on monotone-increase events with `d ≥ 0`; HKL's
    `Prop`-valued INCREASE is sufficient for the §3 data and avoids
    the clamping bookkeeping. -/
def INCREASE {α δ Time : Type*} [Add δ]
    (φ : TimedAdjective α δ Time) (x : α) (d : δ)
    (startT finT : Time) : Prop :=
  φ x startT + d = φ x finT

/-- Zero-duration events (start = end) carry zero difference value. -/
theorem increase_self {α δ Time : Type*} [AddZeroClass δ]
    (φ : TimedAdjective α δ Time) (x : α) (t : Time) :
    INCREASE φ x 0 t t := by
  simp [INCREASE]

/-- HKL §3 thesis at the type level: when the difference value `d` is
    given, the end degree is **uniquely determined** by the start degree
    — the structural source of telic interpretations. -/
theorem increase_unique_end {α δ Time : Type*} [Add δ]
    (φ : TimedAdjective α δ Time) (x : α) (d : δ) (startT finT₁ finT₂ : Time)
    (h₁ : INCREASE φ x d startT finT₁) (h₂ : INCREASE φ x d startT finT₂) :
    φ x finT₁ = φ x finT₂ :=
  h₁.symm.trans h₂

-- ════════════════════════════════════════════════════
-- § 2. Central matrix: scalar structure → default telicity (HKL §3.2)
-- ════════════════════════════════════════════════════

/-! HKL §3.2 (p. 135): **closed-range adjectives** (*full, empty, straight,
    dry*) map to bounded scales; **open-range adjectives** (*long, wide,
    short*) map to unbounded scales. The DA verbs derived from each class
    default to telic vs atelic respectively (HKL eqs 26-27).

    Linglib's fragment encodes this directly via `degreeAchievementScale`
    annotations on each DA verb:

    | Verb        | Base adjective | scaleBoundedness | vendlerClass     |
    |-------------|----------------|------------------|------------------|
    | straighten  | straight       | `.closed`        | `.accomplishment`|
    | lengthen    | long           | `.open_`         | `.activity`      |
    | widen       | wide           | `.open_`         | `.activity`      |
    | cool        | cool           | `.open_`         | `.activity`      |
    | warm        | warm           | `.open_`         | `.activity`      |

    The theorems below verify HKL's matrix prediction on each fragment
    entry. K&L 2008's `KennedyLevin2008.lean` study file proves the
    per-verb derivation of `vendlerClass` from `scaleBoundedness`
    structurally; this file checks HKL's specific predictions on the
    central exemplars. -/

/-- HKL eq 26 (closed-range default): "straighten" — closed scale,
    accomplishment (telic). -/
theorem straighten_closed_accomplishment :
    straighten.toVerbCore.degreeAchievementScale.map (·.scaleBoundedness) =
      some Boundedness.closed ∧
    straighten.toVerbCore.vendlerClass = some .accomplishment := ⟨rfl, rfl⟩

/-- HKL eq 27 (open-range default): "lengthen" — open scale, activity
    (atelic). -/
theorem lengthen_open_activity :
    lengthen.toVerbCore.degreeAchievementScale.map (·.scaleBoundedness) =
      some Boundedness.open_ ∧
    lengthen.toVerbCore.vendlerClass = some .activity := ⟨rfl, rfl⟩

/-- HKL §3.1 default: "widen" — open scale, activity (made telic only by
    overt measure phrase, see §3 below). -/
theorem widen_open_activity :
    widen.toVerbCore.degreeAchievementScale.map (·.scaleBoundedness) =
      some Boundedness.open_ ∧
    widen.toVerbCore.vendlerClass = some .activity := ⟨rfl, rfl⟩

/-- HKL §3.1 default: "cool" — open scale, activity (made telic only by
    overt measure phrase or contextual bound). -/
theorem cool_open_activity :
    cool.toVerbCore.degreeAchievementScale.map (·.scaleBoundedness) =
      some Boundedness.open_ ∧
    cool.toVerbCore.vendlerClass = some .activity := ⟨rfl, rfl⟩

/-- HKL §3.1 default: "warm" — open scale, activity. -/
theorem warm_open_activity :
    warm.toVerbCore.degreeAchievementScale.map (·.scaleBoundedness) =
      some Boundedness.open_ ∧
    warm.toVerbCore.vendlerClass = some .activity := ⟨rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 3. Specifying the difference value (HKL §3.1)
-- ════════════════════════════════════════════════════

/-! HKL §3.1: when the difference value is bounded by overt linguistic
    material, the predicate is telic regardless of the base adjective's
    scalar structure. Three modifier classes:

    1. **Measure phrases** (HKL eqs 18-20): *widened the road 5 m*,
       *cooled 4 degrees* — telic.
    2. **Completely** (HKL eqs 21-22): *straightened completely*,
       *dried completely* — telic. Forces `d` to a maximum.
    3. **Significantly** (HKL eq 23) — telic (lower bound from
       monotone-increasing modifier); contrasts with **slightly**
       (HKL eq 24) — atelic (no lower bound). -/

/-- An HKL §3.1 modifier-class datum: a sentence + its modifier-class +
    HKL's predicted telicity + the paper-equation tag. -/
structure HKLModifierDatum where
  sentence : String
  modifier : String
  expectedTelic : Bool
  paperEq : String
  deriving Repr

def widenedRoad5m : HKLModifierDatum :=
  { sentence := "They widened the road 5 m.", modifier := "5 m",
    expectedTelic := true, paperEq := "HKL eq 18a (telic per eq 19a)" }

def lakeCooled4Deg : HKLModifierDatum :=
  { sentence := "The lake cooled 4 degrees.", modifier := "4 degrees",
    expectedTelic := true, paperEq := "HKL eq 18b (telic per eq 19b)" }

def straightenedCompletely : HKLModifierDatum :=
  { sentence := "They straightened the rope completely.",
    modifier := "completely",
    expectedTelic := true, paperEq := "HKL eq 21a (telic per eq 22a)" }

def driedCompletely : HKLModifierDatum :=
  { sentence := "The clothes dried completely.", modifier := "completely",
    expectedTelic := true, paperEq := "HKL eq 21b (telic per eq 22b)" }

def broadenedSignificantly : HKLModifierDatum :=
  { sentence := "The IC broadened the investigation significantly.",
    modifier := "significantly",
    expectedTelic := true, paperEq := "HKL eq 23a (telic per 23b/c)" }

def broadenedSlightly : HKLModifierDatum :=
  { sentence := "The IC broadened the investigation slightly.",
    modifier := "slightly",
    expectedTelic := false, paperEq := "HKL eq 24a (atelic per 24b/c)" }

def hklSection3_1Data : List HKLModifierDatum :=
  [widenedRoad5m, lakeCooled4Deg, straightenedCompletely, driedCompletely,
   broadenedSignificantly, broadenedSlightly]

/-- Modifier-class licensing prediction (HKL §3.1): measure phrases,
    `completely`, and `significantly` each induce telicity by bounding
    the difference value below; `slightly` does not. Cf. K&M 2005's
    later modifier-class matrix at scale-structure level. -/
def modifierLicensesTelic : String → Bool
  | "completely" => true
  | "significantly" => true
  | "slightly" => false
  | _ => true  -- measure phrases (default for unrecognized modifier strings)

/-- HKL §3.1 matrix: all six §3.1 data points agree with the
    modifier-class prediction. -/
theorem hklSection3_1Data_consistent :
    hklSection3_1Data.all (fun d =>
      modifierLicensesTelic d.modifier == d.expectedTelic) = true := by
  decide

-- ════════════════════════════════════════════════════
-- § 4. Context-dependent telicity (HKL §3.3)
-- ════════════════════════════════════════════════════

/-! HKL §3.3: when no overt linguistic material specifies the difference
    value, real-world knowledge can supply a bound, producing a
    **defeasible** telic interpretation that is **cancellable** because
    it arises through conversational implicature.

    The contrast (HKL eqs 28 vs 30): pants/blinds have a conventional
    maximum → telic (eq 28); commute/heat have no conventional bound →
    atelic (eq 30). Eq 32 confirms the eq-28 telicity is cancellable
    (*lengthened my pants, but not completely* is felicitous). Eq 33
    confirms linguistically-supplied bounds (eq 21's *completely*) are
    NOT cancellable (*#straightened completely, but not completely*). -/

/-- An HKL §3.3 context-dependent telicity datum. -/
structure HKLContextDatum where
  sentence : String
  contextProvidesBound : Bool
  expectedTelic : Bool
  cancellable : Bool
  paperEq : String
  deriving Repr

def tailorLengthened : HKLContextDatum :=
  { sentence := "The tailor lengthened my pants.",
    contextProvidesBound := true, expectedTelic := true, cancellable := true,
    paperEq := "HKL eq 28a (telic per 29a, cancellable per 32a)" }

def kimLowered : HKLContextDatum :=
  { sentence := "Kim lowered the blind.",
    contextProvidesBound := true, expectedTelic := true, cancellable := true,
    paperEq := "HKL eq 28b (telic per 29b)" }

def trafficLengthened : HKLContextDatum :=
  { sentence := "The traffic lengthened my commute.",
    contextProvidesBound := false, expectedTelic := false, cancellable := false,
    paperEq := "HKL eq 30a (atelic per 31a)" }

def kimLoweredHeat : HKLContextDatum :=
  { sentence := "Kim lowered the heat.",
    contextProvidesBound := false, expectedTelic := false, cancellable := false,
    paperEq := "HKL eq 30b (atelic per 31b)" }

def hklSection3_3Data : List HKLContextDatum :=
  [tailorLengthened, kimLowered, trafficLengthened, kimLoweredHeat]

/-- HKL §3.3 matrix prediction: contextual bound ⟺ (defeasible) telicity;
    when telic via context, the inference is cancellable; when no
    context-bound, the interpretation is robustly atelic. -/
theorem hklSection3_3Data_matrix :
    hklSection3_3Data.all (fun d =>
      d.contextProvidesBound == d.expectedTelic &&
      d.contextProvidesBound == d.cancellable) = true := by
  decide

-- ════════════════════════════════════════════════════
-- § 5. Beyond degree achievements (HKL §4.1) — data only
-- ════════════════════════════════════════════════════

/-! HKL §4.1 extends the analysis to **consumption** (*eat the sandwich*,
    eqs 36-37), **motion** (*run a mile*, *descend 1000m*, eqs 38-42),
    and **creation** (*draw a house*, eq 39) — the "classically telic"
    verbs of @cite{krifka-1989}'s incremental-theme tradition. Their
    telicity ALSO depends on the boundedness of a difference value:
    bounded → telic, unbounded → atelic. The difference value is "the
    measure of change along a path of motion, in spatial extent, or in
    some other scalar property" (HKL §4.2).

    HKL uses this generalization to argue against Dowty 1991's
    "incremental theme as argument" view: the incremental theme is
    properly construed as a *property of an argument*, not the
    argument itself (HKL §4.2). That argument is recorded as data here
    but not further formalized — the K89 quantization framework
    (`Theories/Semantics/Events/Krifka1989.lean`) is the substrate for
    the consumption/creation cases, and `Phenomena/TenseAspect/Studies/Krifka1989.lean`
    §1-§4 cover the same ground via Krifka's QUA/CUM apparatus. -/

/-- A datum from HKL §4.1's beyond-DA generalization. -/
structure HKLBeyondDADatum where
  sentence : String
  verbClass : String
  bounded : Bool
  expectedTelic : Bool
  paperEq : String
  deriving Repr

def ateSandwich5min : HKLBeyondDADatum :=
  { sentence := "She ate the sandwich in 5 minutes.",
    verbClass := "consumption",
    bounded := true, expectedTelic := true,
    paperEq := "HKL eq 36 / 37a" }

def ranMile : HKLBeyondDADatum :=
  { sentence := "She ran a mile.", verbClass := "motion",
    bounded := true, expectedTelic := true,
    paperEq := "HKL eq 38a (negation infelicitous)" }

def ranRace : HKLBeyondDADatum :=
  { sentence := "She ran a race.", verbClass := "motion",
    bounded := true, expectedTelic := true,
    paperEq := "HKL eq 38b" }

def planeDescended20min : HKLBeyondDADatum :=
  { sentence := "The plane descended in 20 minutes.",
    verbClass := "directed motion",
    bounded := true, expectedTelic := true,
    paperEq := "HKL eq 41a (cancellable per 41b)" }

def hklSection4Data : List HKLBeyondDADatum :=
  [ateSandwich5min, ranMile, ranRace, planeDescended20min]

/-- HKL §4.1 generalization: across consumption, motion, and directed
    motion, bounded difference value ⟺ telic interpretation. -/
theorem hklSection4Data_bounded_iff_telic :
    hklSection4Data.all (fun d => d.bounded == d.expectedTelic) = true := by
  decide

end HayKennedyLevin1999
