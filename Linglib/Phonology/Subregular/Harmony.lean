/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Subregular.Language.ForbiddenPairs
import Linglib.Phonology.Harmony.Basic
import Linglib.Phonology.Segmental.Basic
import Linglib.Phonology.Subregular.TierRule
import Linglib.Core.Computability.Subregular.Function.OSL

/-!
# Harmony Systems
[rose-walker-2011] [belth-2026]

The [rose-walker-2011] typological lens — a process by which a
distinctive feature value spreads from a **trigger** segment to **target**
segments, optionally skipping **transparent** segments and halting at
**blocker** (opaque) segments.

## Architecture

`System` is a tier-based AGREE rule (the recognizer half — a `TierRule`,
inherited via `extends`) carrying the transduction discipline that turns the
recognizer into a structure-changing map:

```
System  extends TierRule Segment          -- tier / trigger-class / side / relation
        feature   : Feature               -- which feature `transduce` writes
        isTarget  : Segment → Prop         [DecidablePred]   -- segments that undergo it
        isBlocker : Segment → Prop         [DecidablePred]   -- opaque segments
```

The trigger predicate is the inherited `targetIsContext` (not re-stored); the
tier projects out transparent segments; `relation` is `.agree` (dissimilatory
tier patterns use `Disagree` and live outside this typology).

**Harmony is grounded on the subregular transducer hierarchy.** The harmonized
string `System.transduce` is an `OSLRule` (`Subregular`),
so its Output-Strictly-Local class membership is a *theorem* by construction
(`System.transduce_isLeftOSL`), not a post-hoc classification of a hand-rolled
walk ([chandlee-eyraud-heinz-2015]).

**This is the tier-based (TSL/OSL) analysis — one live account, not a settled
reduction.** Vowel harmony is the contested non-local boundary case:
autosegmental spreading ([goldsmith-1976]), Agreement-by-Correspondence
([rose-walker-2004]), and OT SPREAD/ALIGN remain rivals with divergent
predictions on transparency and opacity. The single-tier commitment is not
universally adequate — Uyghur backness harmony is provably non-TSL
([mayer-major-2018]). Only the identity-tier case is currently proved
subsequential (TierRule's non-trivial-tier classification is deferred). The
theory-neutral pattern vocabulary these rival accounts share lives at
`Phonology/Harmony/Basic.lean`.

## Operations

- `harmonyDomain`: the stem portion governing suffix harmony (truncated at a blocker)
- `triggerValue`: dispatch the inherited recognizer on the harmony domain
- `harmonizeOne`: write the predicted value into a single target segment
- `spreadSuffix`: walk a suffix list (a convenience over the recognizer)
- `transduce`: the harmonized-string function, as a 2-OSL transducer

Language instances live in `Fragments/{Turkish,Finnish,Hungarian}/VowelHarmony.lean`.
The pattern-layer bridge `Phonology.Harmony.Pattern.harmonic_iff_mem_tsl` is
also housed here (connection files live in the downstream tree).
-/

namespace Subregular.Harmony

open Phonology (Segment Feature)
open Phonology
open Subregular (OSLRule IsLeftOutputStrictlyLocal)

/-! ### Direction -/

/-- Compile a pattern-level direction (`Phonology.Harmony.Direction`) to the
    side at which the underlying `TierRule` reads its triggering context.
    Bidirectional collapses to rightward operationally (the same
    `harmonyDomain`/`triggerValue` computation handles both); the typological
    distinction lives only at the smart-constructor argument site. -/
def _root_.Phonology.Harmony.Direction.toSide : Phonology.Harmony.Direction → Side
  | .rightward | .bidirectional => .left
  | .leftward => .right

/-! ### System — TierRule + transduction discipline -/

/-- A harmony system: a tier-based AGREE rule (`TierRule`, the recognizer
    half, inherited via `extends`) plus the transduction discipline — which
    segments undergo the change (`isTarget`) and which are opaque blockers
    (`isBlocker`). The trigger predicate is the inherited `targetIsContext`;
    the spreading feature is `feature` (the inherited `featureValue` is
    `fun s => s feature` by construction, set by `mk'`). -/
structure System extends TierRule Segment where
  /-- The distinctive feature that spreads. -/
  feature   : Feature
  /-- Which segments undergo the feature change. -/
  isTarget  : Segment → Prop
  [decTarget' : DecidablePred isTarget]
  /-- Which segments are opaque (impose their own value, re-triggering).
      Default: no blockers. -/
  isBlocker : Segment → Prop := fun _ => False
  [decBlocker : DecidablePred isBlocker]

attribute [instance] System.decTarget' System.decBlocker

/-- Smart constructor exposing the [rose-walker-2011] six-way decomposition,
    compiling it into the inherited `TierRule` plus the transduction fields.
    `Bool`-lambda args stay ergonomic for fragment authors; they are stored as
    the decidable `Prop` fields. Trigger lives only in `targetIsContext` (no
    duplicate field); `featureValue` is derived from `feature`. -/
def System.mk' (feature : Feature)
    (isTrigger isTarget isTransparent : Segment → Bool)
    (direction : Phonology.Harmony.Direction := .rightward)
    (isBlocker : Segment → Bool := fun _ => false) : System where
  toTierRule :=
    { tier := TierProjection.byClass (fun s => !isTransparent s = true)
      side := direction.toSide
      targetIsContext := fun s => isTrigger s = true
      relation := .agree
      featureValue := fun s => s feature
      default := none }
  feature := feature
  isTarget := fun s => isTarget s = true
  isBlocker := fun s => isBlocker s = true

/-! ### Recovering the Rose-Walker Typology -/

/-- The trigger predicate (= the inherited `targetIsContext`). Convenience
    `Bool` accessor for the [rose-walker-2011] typological decomposition;
    decidability is in scope via the inherited `decTarget`. -/
@[inline] def isTrigger (sys : System) (s : Segment) : Bool :=
  decide (sys.targetIsContext s)

/-! ### Harmony Domain -/

/-- The **harmony domain**: the portion of the stem that governs suffix
    harmony. For left-context (rightward / bidirectional) rules, this is
    everything after the last blocker; for right-context (leftward),
    everything before the first blocker. Without blockers, the full stem.

    Example: stem = [a, BLOCKER, i] with rightward spreading →
    domain = [i] (only the suffix-adjacent segment governs). -/
def harmonyDomain (sys : System) (stem : List Segment) : List Segment :=
  match sys.side with
  | .left  => (stem.reverse.takeWhile (fun s => !decide (sys.isBlocker s))).reverse
  | .right => stem.takeWhile (fun s => !decide (sys.isBlocker s))

/-! ### Trigger Value Extraction -/

/-- The harmony value predicted at the suffix slot: dispatch the inherited
    `TierRule` recognizer on the harmony domain.

    *True by construction*: this IS the rule's prediction at the
    suffix-adjacent position, after truncating the stem at the first
    blocker. No bridge theorem is needed — the typological decomposition was
    compiled into the inherited fields by the smart constructor. -/
def triggerValue (sys : System) (stem : List Segment) : Option Bool :=
  let domain := harmonyDomain sys stem
  match sys.side with
  | .left  => sys.toTierRule.apply domain []
  | .right => sys.toTierRule.apply [] domain

/-! ### Segment-Level Harmony -/

/-- Write harmonic value `v` into a segment's `feature` slot. -/
def writeFeature (feature : Feature) (v : Bool) (s : Segment) : Segment :=
  fun f => if f == feature then some v else s f

/-- Apply harmony to a single segment: if the segment is a target, set
    the harmony feature to the given value; otherwise return unchanged. -/
def harmonizeOne (sys : System) (val : Bool) (s : Segment) : Segment :=
  if sys.isTarget s then writeFeature sys.feature val s else s

/-! ### Suffix Spreading (convenience over the recognizer) -/

/-- Apply harmony through a suffix segment list, respecting blockers.
    Walks left-to-right: a **blocker** halts (this and subsequent segments
    unchanged); a **target** is harmonized and spreading continues; anything
    else passes through. Without blockers this maps `harmonizeOne` over the
    suffix. For the genuine subregular semantics (blockers re-trigger), see
    `transduce`. -/
def spreadSuffix (sys : System) (val : Bool)
    (suffix : List Segment) : List Segment :=
  match suffix with
  | [] => []
  | s :: rest =>
    if sys.isBlocker s then s :: rest
    else harmonizeOne sys val s :: spreadSuffix sys val rest

/-! ### Transducer grounding — harmony as an OSL function -/

/-- Harmony as a **2-Output-Strictly-Local rule** ([chandlee-eyraud-heinz-2015]):
    scanning left-to-right, each target takes the harmonic value of the
    immediately preceding *output* segment (the propagated value); blockers and
    non-targets emit unchanged, and a blocker's own value enters the output
    window — so subsequent targets re-trigger from the blocker. This is the
    genuine subregular object harmony computes. -/
def System.spreadRule (sys : System) : OSLRule 2 Segment Segment where
  windowOutput window s :=
    if sys.isBlocker s then [s]
    else if sys.isTarget s then
      match window.getLast? with
      | some prev =>
        match prev sys.feature with
        | some v => [writeFeature sys.feature v s]
        | none   => [s]
      | none => [s]
    else [s]

/-- The harmonized-string function of a harmony system: the OSL transduction. -/
def System.transduce (sys : System) : List Segment → List Segment :=
  sys.spreadRule.apply

/-- **The harmonized string is a 2-OSL function by construction.** Subregular
    class membership is a theorem about the transducer, not a post-hoc
    classification of a hand-rolled walk. -/
theorem System.transduce_isLeftOSL (sys : System) :
    IsLeftOutputStrictlyLocal 2 sys.transduce :=
  sys.spreadRule.isLeftOutputStrictlyLocal_apply

/-! ### Properties -/

/-- Non-target segments are unchanged by harmonization. -/
theorem harmonizeOne_nontarget {sys : System} {val : Bool} {s : Segment}
    (h : ¬ sys.isTarget s) :
    harmonizeOne sys val s = s := by
  unfold harmonizeOne; rw [if_neg h]

/-- Spreading through an empty suffix returns an empty list. -/
theorem spreadSuffix_nil (sys : System) (val : Bool) :
    spreadSuffix sys val [] = [] := rfl

/-- Suffix length is preserved by spreading (even with blockers — blocked
    segments are returned unchanged, not removed). -/
theorem spreadSuffix_length (sys : System) (val : Bool)
    (suffix : List Segment) :
    (spreadSuffix sys val suffix).length = suffix.length := by
  induction suffix with
  | nil => rfl
  | cons s rest ih =>
    simp only [spreadSuffix]
    split
    · rfl
    · simp [ih]

/-- The harmony domain is the full stem when there are no blockers. -/
theorem harmonyDomain_no_blockers (sys : System) (stem : List Segment)
    (h : ∀ s ∈ stem, ¬ sys.isBlocker s) :
    harmonyDomain sys stem = stem := by
  unfold harmonyDomain
  have hpred : ∀ s ∈ stem, (!decide (sys.isBlocker s)) = true :=
    fun s hs => by simp [h s hs]
  have hrev : ∀ s ∈ stem.reverse, (!decide (sys.isBlocker s)) = true :=
    fun s hs => hpred s (List.mem_reverse.mp hs)
  split
  · rw [List.takeWhile_eq_self_iff.mpr hrev, List.reverse_reverse]
  · exact List.takeWhile_eq_self_iff.mpr hpred

/-- Blockers in the suffix halt spreading: segments at and after the first
    blocker are returned unchanged. -/
theorem spreadSuffix_blocker (sys : System) (val : Bool)
    (s : Segment) (rest : List Segment) (hb : sys.isBlocker s) :
    spreadSuffix sys val (s :: rest) = s :: rest := by
  simp [spreadSuffix, hb]

/-! ### Patterns are TSL₂ -/

end Subregular.Harmony

namespace Phonology.Harmony

open Subregular TSLGrammar

variable {α V : Type*}

/-- **Harmony is TSL₂ by construction** ([aksenova-rawski-graf-heinz-2024]):
    a pattern's surface harmonicity is membership in the tier-based strictly
    2-local grammar whose tier is `Pattern.OnTier` and whose banned bigrams
    are the incompatible pairs. Strictly local grammars cannot express harmony
    (unbounded distance) and strictly piecewise grammars cannot express
    blocking; the tier-based class captures both. -/
theorem Pattern.harmonic_iff_mem_tsl (p : Pattern α V) (w : List α) :
    p.Harmonic w ↔ w ∈ (ofForbiddenPairs (¬ p.Compatible · ·) p.OnTier).lang := by
  simp only [mem_ofForbiddenPairs_lang_iff_filter_isChain, Pattern.Harmonic, Pattern.tier, not_not]

end Phonology.Harmony
