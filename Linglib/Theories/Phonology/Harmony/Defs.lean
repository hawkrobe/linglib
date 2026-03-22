import Linglib.Theories.Phonology.Features

/-!
# Harmony Systems
@cite{rose-walker-2011}

General framework for phonological harmony following @cite{rose-walker-2011}:
a process by which a distinctive feature value spreads from a **trigger**
segment to **target** segments, optionally skipping **transparent** segments
and halting at **blocker** (opaque) segments.

## Components (§1)

1. **Feature**: which distinctive feature spreads ([back], [round], [ATR], ...)
2. **Trigger**: which segments source the spreading feature value
3. **Target**: which segments receive the spreading feature value
4. **Transparent**: which segments are skipped without blocking
5. **Blocker**: which segments halt spreading (opaque segments)
6. **Direction**: rightward, leftward, or bidirectional

## Operations

- `harmonyDomain`: extract the spreading domain (stem segments not separated
  from the suffix by a blocker)
- `triggerValue`: extract the harmony value from the domain (direction-aware)
- `harmonizeOne`: apply harmony to a single segment
- `spreadSuffix`: apply harmony through a suffix, halting at blockers
## Instances

- **Turkish palatal harmony**: [back] from last stem vowel → all suffix vowels
- **Turkish labial harmony**: [round] from last stem vowel → high suffix vowels only
- **Finnish palatal harmony**: [back] from last harmonic stem vowel → non-neutral
  suffix vowels; neutral vowels (/e/, /i/) are transparent
- **Hungarian palatal harmony**: [back] from last harmonic stem vowel → non-neutral
  suffix vowels; neutral vowels (/i, í, e, é/) are transparent
-/

namespace Theories.Phonology.Harmony

open Theories.Phonology (Segment Feature FeatureVal)

-- ============================================================================
-- § 1: Harmony System Type
-- ============================================================================

/-- Direction of harmony spreading. -/
inductive HarmonyDir where
  | rightward     -- stem → suffix (standard for suffix-controlled VH)
  | leftward      -- suffix → stem (dominant-recessive systems)
  | bidirectional -- both directions from trigger
  deriving DecidableEq, BEq, Repr

/-- A parameterized harmony system.

    Following @cite{rose-walker-2011}'s decomposition into trigger, target,
    domain, and spreading feature. Each language's vowel harmony is an
    instance of this type.

    The `isBlocker` field (default: no blockers) identifies **opaque**
    segments that halt spreading. In Hungarian, low neutral vowels like
    /e/ sometimes block back harmony from passing through — marking /e/
    as a blocker rather than transparent yields different predictions for
    stems like *hotel*. -/
structure HarmonySystem where
  /-- The distinctive feature that spreads. -/
  feature       : Feature
  /-- Trigger predicate: which segments source the feature value. -/
  isTrigger     : Segment → Bool
  /-- Target predicate: which segments undergo feature change. -/
  isTarget      : Segment → Bool
  /-- Transparency predicate: which segments are skipped during spreading
      without blocking it. -/
  isTransparent : Segment → Bool
  /-- Blocker predicate: which segments halt spreading (opaque).
      Default: no blockers. -/
  isBlocker     : Segment → Bool := (λ _ => false)
  /-- Direction of spreading. -/
  direction     : HarmonyDir

-- ============================================================================
-- § 2: Harmony Domain
-- ============================================================================

/-- The **harmony domain**: the portion of the stem that governs suffix
    harmony. For rightward spreading, this is everything after the last
    blocker; for leftward, everything before the first blocker.

    Without blockers, the domain is the full stem.

    Example: stem = [a, BLOCKER, i] with rightward spreading →
    domain = [i] (only the suffix-adjacent segment governs). -/
def harmonyDomain (sys : HarmonySystem) (stem : List Segment) : List Segment :=
  match sys.direction with
  | .rightward | .bidirectional =>
    (stem.reverse.takeWhile (fun s => !sys.isBlocker s)).reverse
  | .leftward =>
    stem.takeWhile (fun s => !sys.isBlocker s)

-- ============================================================================
-- § 3: Trigger Value Extraction
-- ============================================================================

/-- Extract the harmony trigger value from a segment sequence.

    1. Restrict to the harmony domain (respecting blockers)
    2. Filter for trigger segments within the domain
    3. Select the **last** trigger (rightward/bidirectional) or **first**
       trigger (leftward)
    4. Return the trigger's value for the harmony feature

    Returns `none` if no trigger is found in the domain (e.g., stems
    with only neutral vowels, or stems where a blocker separates all
    triggers from the suffix boundary). -/
def triggerValue (sys : HarmonySystem) (stem : List Segment) : Option Bool :=
  let domain := harmonyDomain sys stem
  let triggers := domain.filter sys.isTrigger
  let t := match sys.direction with
    | .rightward | .bidirectional => triggers.getLast?
    | .leftward => triggers.head?
  t.bind (·.spec sys.feature)

-- ============================================================================
-- § 4: Segment-Level Harmony
-- ============================================================================

/-- Apply harmony to a single segment: if the segment is a target, set
    the harmony feature to the given value; otherwise return unchanged. -/
def harmonizeOne (sys : HarmonySystem) (val : Bool) (s : Segment) : Segment :=
  if sys.isTarget s then
    { spec := λ f => if f == sys.feature then some val else s.spec f }
  else s

-- ============================================================================
-- § 5: Suffix Spreading
-- ============================================================================

/-- Apply harmony through a suffix segment list, respecting blockers.

    Walks through segments left-to-right:
    - **Blocker**: halts spreading — this segment and all subsequent segments
      are returned unchanged.
    - **Target**: harmonized (feature value set) and spreading continues.
    - **Other** (transparent/inert): returned unchanged and spreading continues.

    Without blockers (default), this reduces to mapping `harmonizeOne`
    over the suffix. -/
def spreadSuffix (sys : HarmonySystem) (val : Bool)
    (suffix : List Segment) : List Segment :=
  match suffix with
  | [] => []
  | s :: rest =>
    if sys.isBlocker s then s :: rest
    else harmonizeOne sys val s :: spreadSuffix sys val rest

-- ============================================================================
-- § 6: Properties
-- ============================================================================

/-- Non-target segments are unchanged by harmonization. -/
theorem harmonizeOne_nontarget {sys : HarmonySystem} {val : Bool} {s : Segment}
    (h : sys.isTarget s = false) :
    harmonizeOne sys val s = s := by
  unfold harmonizeOne; simp [h]

/-- Spreading through an empty suffix returns an empty list. -/
theorem spreadSuffix_nil (sys : HarmonySystem) (val : Bool) :
    spreadSuffix sys val [] = [] := rfl

/-- Suffix length is preserved by spreading (even with blockers — blocked
    segments are returned unchanged, not removed). -/
theorem spreadSuffix_length (sys : HarmonySystem) (val : Bool)
    (suffix : List Segment) :
    (spreadSuffix sys val suffix).length = suffix.length := by
  induction suffix with
  | nil => rfl
  | cons s rest ih =>
    simp only [spreadSuffix]
    split
    · rfl
    · simp [ih]

/-- Helper: `takeWhile p l = l` when `p` holds for all elements. -/
private theorem takeWhile_all {l : List Segment} {p : Segment → Bool}
    (h : ∀ s ∈ l, p s = true) : l.takeWhile p = l := by
  induction l with
  | nil => rfl
  | cons a t ih =>
    simp [h a (.head _), ih (fun s hs => h s (.tail _ hs))]

/-- The harmony domain is the full stem when there are no blockers. -/
theorem harmonyDomain_no_blockers (sys : HarmonySystem) (stem : List Segment)
    (h : ∀ s ∈ stem, sys.isBlocker s = false) :
    harmonyDomain sys stem = stem := by
  unfold harmonyDomain
  have hpred : ∀ s ∈ stem, (!sys.isBlocker s) = true :=
    fun s hs => by simp [h s hs]
  have hrev : ∀ s ∈ stem.reverse, (!sys.isBlocker s) = true :=
    fun s hs => hpred s (List.mem_reverse.mp hs)
  split
  · rw [takeWhile_all hrev, List.reverse_reverse]  -- rightward
  · rw [takeWhile_all hrev, List.reverse_reverse]  -- bidirectional
  · exact takeWhile_all hpred                       -- leftward

/-- Blockers in the suffix halt spreading: segments at and after the first
    blocker are returned unchanged. -/
theorem spreadSuffix_blocker (sys : HarmonySystem) (val : Bool)
    (s : Segment) (rest : List Segment) (hb : sys.isBlocker s = true) :
    spreadSuffix sys val (s :: rest) = s :: rest := by
  simp [spreadSuffix, hb]

end Theories.Phonology.Harmony
