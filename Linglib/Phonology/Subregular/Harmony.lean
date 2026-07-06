/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Core.Computability.Lens
import Linglib.Core.Computability.Subregular.Language.ForbiddenPairs
import Linglib.Phonology.Harmony.Basic
import Linglib.Phonology.Segmental.Basic
import Linglib.Phonology.Subregular.TierRule
import Linglib.Core.Computability.Subregular.Function.OSL

/-!
# Harmony systems

A harmony system in the [rose-walker-2011] typological decomposition: a
distinctive feature value spreads from trigger segments to target segments,
optionally skipping transparent segments and halting at opaque blockers
([rose-walker-2011], [belth-2026]). `System` couples the tier-based AGREE
recognizer with the transduction discipline that turns it into a
structure-changing map.

`System` is alphabet-generic; at each concrete alphabet it instantiates to a
familiar finite-state object — `transduce` to a subsequential transducer whose
only state is one lens readout (at Turkish's alphabet, the classic two-state
front/back machine), the recognizer to a last-trigger-decides subsequential
function. The theorems are proved once, generically; every instantiation
inherits them. Finiteness is supplied at instantiation, not in the structure
(mathlib's `DFA` convention: `[Fintype α]` appears only on the theorems that
consume it).

## Main definitions

* `Subregular.Harmony.System`: a `Phonology.Harmony.Pattern` plus the
  mechanism-side residue — trigger context, targets, and the feature write.
  The valuation and write form a lawful lens (`System.lens`, a `Lens`);
  blockers, the tier, and the recognizer (`System.toTierRule`) are derived
  from the pattern; `System.mk'` compiles the six-way decomposition.
* `Subregular.Harmony.harmonyDomain`, `triggerValue`: the stem portion
  governing suffix harmony, and the recognizer's prediction over it.
* `System.transduce`: the harmonized-string function, as a 2-OSL rule
  ([chandlee-eyraud-heinz-2015]).

## Main results

* `System.transduce_isLeftOSL`: the harmonized string is 2-OSL by
  construction, not by post-hoc classification.
* `Phonology.Harmony.Pattern.harmonic_iff_mem_tsl`: a pattern's surface
  harmonicity is membership in a TSL₂ language
  ([aksenova-rawski-graf-heinz-2024]).

## Implementation notes

This is the tier-based (TSL/OSL) analysis — one live account, not a settled
reduction: autosegmental spreading ([goldsmith-1976]),
Agreement-by-Correspondence ([rose-walker-2004]), and OT SPREAD/ALIGN remain
rivals with divergent predictions on transparency and opacity, and the
single-tier commitment is not universally adequate — Uyghur backness harmony
is provably non-TSL ([mayer-major-2018]). Only the identity-tier case is
currently proved subsequential. The theory-neutral pattern vocabulary the
rival accounts share lives in `Phonology/Harmony/Basic.lean`; language
instances live in `Fragments/{Turkish,Finnish,Hungarian}/VowelHarmony.lean`.
-/

/-! ### Direction -/

namespace Phonology.Harmony

/-- Compile a direction to the `TierRule` context side (bidirectional ↦ rightward). -/
def Direction.toSide : Direction → Subregular.Side
  | .rightward | .bidirectional => .left
  | .leftward => .right

end Phonology.Harmony

namespace Subregular.Harmony

open Phonology (Segment Feature)
open Phonology.Harmony (Pattern)

/-! ### System — a pattern plus its transduction discipline -/

/-- Write harmonic value `v` into a segment's `feature` slot: the function-type
    lens (`Lens.proj`) written at `feature`. -/
def writeFeature (feature : Feature) (v : Bool) (s : Segment) : Segment :=
  Function.update s feature (some v)

/-- A harmony system: the descriptive `Phonology.Harmony.Pattern` (valuation,
    blockers, transparency, direction) plus the mechanism-side residue — the
    trigger context, the targets, and the feature write. -/
structure System (α : Type*) where
  /-- The descriptive pattern the system realizes. -/
  pattern : Pattern α Bool
  /-- The natural class of triggering context segments. -/
  targetIsContext : α → Prop
  [decContext : DecidablePred targetIsContext]
  /-- Which segments undergo the feature change. -/
  isTarget : α → Prop
  [decTarget' : DecidablePred isTarget]
  /-- Write the harmonic value into a segment. -/
  write : Bool → α → α
  /-- Reading back a written value gives that value. -/
  value_write : ∀ v s, pattern.value (write v s) = some v

attribute [instance] System.decContext System.decTarget'

variable {α : Type*} (sys : System α) (val : Bool)

/-- Opaque blockers, read off the pattern. -/
def System.isBlocker (s : α) : Prop :=
  sys.pattern.participation s = .opaque

instance : DecidablePred sys.isBlocker := fun s => by
  unfold System.isBlocker; infer_instance

/-- The system's lens: `(pattern.value, write)` with the put-get law. The slot
    readout is the only state the OSL transducer carries. -/
def System.lens : Lens α Bool :=
  ⟨sys.pattern.value, sys.write, sys.value_write⟩

/-- The recognizer core, derived from the pattern: an agree `TierRule` over the
    pattern's tier, reading the pattern's valuation from the pattern's side. -/
def System.toTierRule : TierRule α where
  tier := TierProjection.byClass sys.pattern.OnTier
  side := sys.pattern.direction.toSide
  targetIsContext := sys.targetIsContext
  relation := .agree
  featureValue := sys.pattern.value
  default := none

/-- Compile the [rose-walker-2011] six-way decomposition into a `System`;
    `Bool` lambdas are stored as the decidable `Prop` fields. -/
def System.mk' (feature : Feature)
    (isTrigger isTarget isTransparent : Segment → Bool)
    (direction : Phonology.Harmony.Direction := .rightward)
    (isBlocker : Segment → Bool := fun _ => false) : System Segment where
  pattern :=
    { value := fun s => s feature
      participation := fun s =>
        if isBlocker s then .opaque
        else if isTransparent s then .transparent
        else .participating
      direction := direction }
  targetIsContext := fun s => isTrigger s = true
  isTarget := fun s => isTarget s = true
  write := writeFeature feature
  value_write := fun v s => by simp [writeFeature]

/-! ### Recovering the Rose-Walker Typology -/

/-- The trigger predicate: `Bool` accessor for `targetIsContext`. -/
@[inline] def isTrigger (s : α) : Bool :=
  decide (sys.targetIsContext s)

/-! ### Harmony Domain -/

/-- The stem portion governing suffix harmony: everything after (rightward) or
    before (leftward) the blocker nearest the suffix. -/
def harmonyDomain (stem : List α) : List α :=
  match sys.pattern.direction.toSide with
  | .left  => (stem.reverse.takeWhile (fun s => !decide (sys.isBlocker s))).reverse
  | .right => stem.takeWhile (fun s => !decide (sys.isBlocker s))

/-! ### Trigger Value Extraction -/

/-- The harmony value predicted at the suffix slot: the recognizer applied to
    the harmony domain. -/
def triggerValue (stem : List α) : Option Bool :=
  let domain := harmonyDomain sys stem
  match sys.pattern.direction.toSide with
  | .left  => sys.toTierRule.apply domain []
  | .right => sys.toTierRule.apply [] domain

/-! ### Segment-Level Harmony -/

/-- Set a target's harmony feature to the given value; non-targets are unchanged. -/
def harmonizeOne (s : α) : α :=
  if sys.isTarget s then sys.write val s else s

/-! ### Suffix Spreading (convenience over the recognizer) -/

/-- Walk a suffix: blockers halt spreading, targets harmonize, all else passes
    through. For the re-triggering subregular semantics, see `transduce`. -/
def spreadSuffix (suffix : List α) : List α :=
  match suffix with
  | [] => []
  | s :: rest =>
    if sys.isBlocker s then s :: rest
    else harmonizeOne sys val s :: spreadSuffix rest

/-! ### Transducer grounding — harmony as an OSL function -/

/-- Harmony as a 2-OSL rule ([chandlee-eyraud-heinz-2015]): each target copies
    the harmonic value of the preceding output segment; blockers re-trigger. -/
def System.spreadRule : OSLRule 2 α α where
  windowOutput window s :=
    if sys.isBlocker s then [s]
    else if sys.isTarget s then
      match window.getLast? with
      | some prev =>
        match sys.pattern.value prev with
        | some v => [sys.write v s]
        | none   => [s]
      | none => [s]
    else [s]

/-- The harmonized-string function of a harmony system: the OSL transduction. -/
def System.transduce : List α → List α :=
  sys.spreadRule.apply

/-- The harmonized string is 2-OSL by construction. -/
theorem System.transduce_isLeftOSL :
    IsLeftOutputStrictlyLocal 2 sys.transduce :=
  sys.spreadRule.isLeftOutputStrictlyLocal_apply

/-! ### Properties -/

variable {sys val}

/-- Non-target segments are unchanged by harmonization. -/
theorem harmonizeOne_nontarget {s : α} (h : ¬ sys.isTarget s) :
    harmonizeOne sys val s = s :=
  if_neg h

/-- Spreading through an empty suffix returns an empty list. -/
theorem spreadSuffix_nil : spreadSuffix sys val [] = [] := rfl

/-- Spreading preserves length: blocked segments are kept, not removed. -/
theorem spreadSuffix_length (suffix : List α) :
    (spreadSuffix sys val suffix).length = suffix.length := by
  induction suffix with
  | nil => rfl
  | cons s rest ih => simp only [spreadSuffix]; split <;> simp [ih]

/-- The harmony domain is the full stem when there are no blockers. -/
theorem harmonyDomain_no_blockers {stem : List α}
    (h : ∀ s ∈ stem, ¬ sys.isBlocker s) :
    harmonyDomain sys stem = stem := by
  unfold harmonyDomain
  split
  · rw [List.takeWhile_eq_self_iff.mpr (by simp_all), List.reverse_reverse]
  · exact List.takeWhile_eq_self_iff.mpr (by simp_all)

/-- A leading blocker halts spreading: the suffix is returned unchanged. -/
theorem spreadSuffix_blocker {s : α} {rest : List α}
    (hb : sys.isBlocker s) :
    spreadSuffix sys val (s :: rest) = s :: rest := by
  simp [spreadSuffix, hb]

/-! ### Patterns are TSL₂

Strictly local grammars cannot express harmony (unbounded distance) and
strictly piecewise grammars cannot express blocking; the tier-based class
captures both ([aksenova-rawski-graf-heinz-2024]). -/

end Subregular.Harmony

namespace Phonology.Harmony

open Subregular TSLGrammar

variable {α V : Type*}

/-- Harmony is TSL₂ by construction. -/
theorem Pattern.harmonic_iff_mem_tsl (p : Pattern α V) (w : List α) :
    p.Harmonic w ↔ w ∈ (ofForbiddenPairs (¬ p.Compatible · ·) p.OnTier).lang := by
  simp only [mem_ofForbiddenPairs_lang_iff_filter_isChain, Pattern.Harmonic, Pattern.tier, not_not]

end Phonology.Harmony
