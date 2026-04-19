import Linglib.Theories.Phonology.Featural.Features
import Linglib.Theories.Phonology.Process.Alternation

/-!
# Harmony Systems
@cite{rose-walker-2011} @cite{belth-2026}

The @cite{rose-walker-2011} typological lens — a process by which a
distinctive feature value spreads from a **trigger** segment to **target**
segments, optionally skipping **transparent** segments and halting at
**blocker** (opaque) segments.

## Architecture

A `HarmonySystem` is a thin typological wrapper around a *tier-based
agreement rule* (the formal core, à la @cite{belth-2026} / Heinz-style
TSL phonology):

```
HarmonySystem  =  rule      : Phonology.Alternation.TierRule Segment   -- value prediction
                 isTarget   : Segment → Bool                           -- spreading discipline
                 isBlocker  : Segment → Bool                           -- iteration halt
                 feature    : Phonology.Feature                        -- which Feature for harmonizeOne
```

The `rule` field IS the formal pattern. Its tier projects out transparent
segments; its context class is the trigger predicate; its relation is
`.agree` (harmony is by definition assimilatory — dissimilatory tier
patterns like Latin liquid dissimilation use `Disagree` and live outside
this typology). `isTarget`/`isBlocker` are the *spreading discipline* —
which segments accept the predicted value and where iteration halts.

Why this shape: in the modern computational/learnability framing
(@cite{belth-2026} and the TSL literature), the tier projection plus a
local rule on it is the central object; the Rose-Walker typological
decomposition (trigger / target / transparent / blocker / direction) is
the descriptive lens for cataloguing what languages do, not a separate
formal primitive. So harmony systems *contain* tier rules rather than
*reducing to them via a bridge theorem* — the relationship is
true-by-construction.

## Components (§1) of @cite{rose-walker-2011}

The smart constructor `HarmonySystem.mk'` exposes exactly Rose-Walker's
six-way decomposition:

1. **Feature**: which distinctive feature spreads ([back], [round], [ATR], ...)
2. **Trigger**: which segments source the spreading feature value
3. **Target**: which segments receive the spreading feature value
4. **Transparent**: which segments are skipped without blocking
5. **Blocker**: which segments halt spreading (opaque segments)
6. **Direction**: rightward, leftward, or bidirectional

It compiles these into the underlying `TierRule` plus the application
fields. After construction, the typology is recoverable: trigger =
`rule.targetIsContext`, transparency is encoded in `rule.tier`, etc.

## Operations

- `harmonyDomain`: extract the spreading domain (stem segments not
  separated from the harmonic edge by a blocker)
- `triggerValue`: dispatch the rule on the harmony domain
  (true-by-construction equivalent to "find the trigger and read off its
  feature value")
- `harmonizeOne`: apply the predicted value to a single segment
- `spreadSuffix`: walk a suffix list, halting at blockers

## Instances

- **Turkish palatal harmony**: [back] from last stem vowel → all suffix vowels
- **Turkish labial harmony**: [round] from last stem vowel → high suffix vowels only
- **Finnish palatal harmony**: [back] from last harmonic stem vowel →
  non-neutral suffix vowels; neutral vowels (/e/, /i/) are transparent
- **Hungarian palatal harmony**: [back] from last harmonic stem vowel →
  non-neutral suffix vowels; neutral vowels (/i, í, e, é/) are transparent
-/

namespace Phonology.Harmony

open Phonology (Segment Feature FeatureVal)
open Phonology.Alternation

-- ============================================================================
-- § 1: Direction
-- ============================================================================

/-- Direction of harmony spreading (Rose-Walker typological label). -/
inductive HarmonyDir where
  | rightward     -- stem → suffix (standard for suffix-controlled VH)
  | leftward      -- suffix → stem (dominant-recessive systems)
  | bidirectional -- both directions from trigger
  deriving DecidableEq, Repr

/-- Compile a typological direction to the side at which the underlying
    `TierRule` reads its triggering context. Bidirectional collapses to
    rightward operationally (the same `harmonyDomain`/`triggerValue`
    computation handles both); the typological distinction lives only at
    the smart-constructor argument site. -/
def HarmonyDir.toSide : HarmonyDir → Side
  | .rightward | .bidirectional => .left
  | .leftward => .right

-- ============================================================================
-- § 2: HarmonySystem — TierRule + Spreading Discipline
-- ============================================================================

/-- A harmony system in the @cite{rose-walker-2011} typological sense.

    Structurally a `TierRule` (the value-prediction half — @cite{belth-2026}'s
    tier-based AGREE rule) bundled with an application policy (which
    segments accept the change, which halt iteration). The `feature` field
    is the `Phonology.Feature` whose value `harmonizeOne`/`spreadSuffix`
    write into target segments; by convention `rule.featureValue s = s.spec
    feature` (enforced by the `mk'` smart constructor; not a typed
    invariant — direct record construction can break it). -/
structure HarmonySystem where
  /-- The distinctive feature that spreads. -/
  feature   : Feature
  /-- The underlying tier-based AGREE rule (the formal core). -/
  rule      : TierRule Segment
  /-- Target predicate: which segments undergo feature change. -/
  isTarget  : Segment → Bool
  /-- Blocker predicate: which segments halt spreading (opaque).
      Default: no blockers. -/
  isBlocker : Segment → Bool := (λ _ => false)

/-- Smart constructor exposing Rose-Walker's six-way decomposition.

    Compiles directly into the underlying `TierRule`:
    - tier projects out transparent segments
    - side is determined by `direction` (rightward/bidirectional ↦ left
      context; leftward ↦ right context)
    - context class is the trigger predicate
    - relation is `.agree` (harmony is assimilatory by definition)
    - feature value extraction reads `s.spec feature`
    - default is `none` (no Elsewhere fallback) -/
def HarmonySystem.mk'
    (feature : Feature)
    (isTrigger isTarget isTransparent : Segment → Bool)
    (direction : HarmonyDir := .rightward)
    (isBlocker : Segment → Bool := (λ _ => false)) : HarmonySystem where
  feature := feature
  rule := {
    tier := Core.Tier.byClass (fun s => !isTransparent s)
    side := direction.toSide
    targetIsContext := isTrigger
    relation := .agree
    featureValue := fun s => s.spec feature
    default := none }
  isTarget := isTarget
  isBlocker := isBlocker

-- ============================================================================
-- § 3: Recovering the Rose-Walker Typology
-- ============================================================================

/-- The trigger predicate (= the rule's context class). Convenience accessor
    for the @cite{rose-walker-2011} typological decomposition. -/
@[inline] def isTrigger (sys : HarmonySystem) (s : Segment) : Bool :=
  sys.rule.targetIsContext s

-- ============================================================================
-- § 4: Harmony Domain
-- ============================================================================

/-- The **harmony domain**: the portion of the stem that governs suffix
    harmony. For left-context (rightward / bidirectional) rules, this is
    everything after the last blocker; for right-context (leftward),
    everything before the first blocker.

    Without blockers, the domain is the full stem.

    Example: stem = [a, BLOCKER, i] with rightward spreading →
    domain = [i] (only the suffix-adjacent segment governs). -/
def harmonyDomain (sys : HarmonySystem) (stem : List Segment) : List Segment :=
  match sys.rule.side with
  | .left  => (stem.reverse.takeWhile (fun s => !sys.isBlocker s)).reverse
  | .right => stem.takeWhile (fun s => !sys.isBlocker s)

-- ============================================================================
-- § 5: Trigger Value Extraction
-- ============================================================================

/-- The harmony value predicted at the suffix slot: dispatch the
    underlying `TierRule` on the harmony domain.

    *True by construction*: this IS the rule's prediction at the
    suffix-adjacent position, after truncating the stem at the first
    blocker. No bridge theorem is needed (and none exists) — the
    typological decomposition was just compiled into the rule's fields by
    the smart constructor. -/
def triggerValue (sys : HarmonySystem) (stem : List Segment) : Option Bool :=
  let domain := harmonyDomain sys stem
  match sys.rule.side with
  | .left  => sys.rule.apply domain []
  | .right => sys.rule.apply [] domain

-- ============================================================================
-- § 6: Segment-Level Harmony
-- ============================================================================

/-- Apply harmony to a single segment: if the segment is a target, set
    the harmony feature to the given value; otherwise return unchanged. -/
def harmonizeOne (sys : HarmonySystem) (val : Bool) (s : Segment) : Segment :=
  if sys.isTarget s then
    { spec := λ f => if f == sys.feature then some val else s.spec f }
  else s

-- ============================================================================
-- § 7: Suffix Spreading
-- ============================================================================

/-- Apply harmony through a suffix segment list, respecting blockers.

    Walks through segments left-to-right:
    - **Blocker**: halts spreading — this segment and all subsequent
      segments are returned unchanged.
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
-- § 8: Properties
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
  · rw [takeWhile_all hrev, List.reverse_reverse]
  · exact takeWhile_all hpred

/-- Blockers in the suffix halt spreading: segments at and after the first
    blocker are returned unchanged. -/
theorem spreadSuffix_blocker (sys : HarmonySystem) (val : Bool)
    (s : Segment) (rest : List Segment) (hb : sys.isBlocker s = true) :
    spreadSuffix sys val (s :: rest) = s :: rest := by
  simp [spreadSuffix, hb]

end Phonology.Harmony
