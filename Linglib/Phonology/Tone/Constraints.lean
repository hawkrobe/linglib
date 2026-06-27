/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.Floating
import Linglib.Phonology.Tone.Basic
import Linglib.Phonology.OptimalityTheory.DirectionalTableau

/-!
# Tonal constraints

OT/HS constraint constructors over the `FloatingForm S TRN` autosegmental
representation (`Phonology/Autosegmental/Floating.lean`), generic over the segment
type `S`. Each is a `Constraint` carrying its own `TermOrder`: genuinely
directional ones (`*FLOAT^→`) emit an indicator vector compared under `.lex`,
while counting ones emit a `[count]` singleton compared under `.degree` (via
`.ofCount`). Equation numbers below are [mcpherson-lamont-2026]'s.

## Main definitions

* `starFloat` / `starFloatCount` — `*FLOAT` (eq. 16): position-aware indicator vs. count variant
* `starTautDock` — `*TAUTDOCK` (eq. 15, after [wolf-2007])
* `starCrowd` — `*CROWD` (eq. 5): per-morpheme tone-count ceiling
* `starFall` — `*FALL` (eq. 23): falling-contour ban
* `starMlessL` — `*M<L` (eq. 29): M immediately before L on the tier
* `maxTone` / `depLinkTone` / `maxLinkTone` — `MAX(T)` / `DEP(link)/T` / `MAX(link)/T` (eq. 7)
* `haveTone` — `HAVETONE` (eq. 17)
* `integrityTone` — `INTEGRITY` ([akinbo-fwangwar-2026]; [mccarthy-prince-1995])

## Implementation notes

Faithfulness (`maxTone`, `maxLinkTone`, `depLinkTone`) compares surface state to the
immutable underlying state stored in `FloatingForm`. Without that underlying-form
tracking, faithfulness can't fire and the [mcpherson-lamont-2026] LR-vs-RL multi-step
asymmetry collapses.

`starFloat` (a position-aware indicator vector under `.lex`) and `starFloatCount`
(the total count under `.degree`) agree on at most one floating tone but diverge as
the set grows: degree comparison cannot tell "delete leftmost" from "delete rightmost"
— [mcpherson-lamont-2026]'s eq. (62) divergent tie. The parallel-vs-directional split
is the constraint's `order` (`.degree` vs. `.lex`), per [lamont-2022b]'s reframing of
directionality as a property of EVAL; the right-to-left case is `.revLex`.
-/

namespace Tone

open Autosegmental
open Tone (TRN)
open Constraints OptimalityTheory

variable {S : Type*} [DecidableEq S] (f : FloatingForm S TRN)

/-! ### Tone-value predicate

Link faithfulness (`FloatingForm.IsInsertedLink` / `IsDeletedLink`) and the morpheme
accessors (`upperMorpheme?` / `lowerMorpheme?` / `morphemes`) are tone-agnostic and live
on `FloatingForm`; only the `TRN`-reading predicate is here. -/

/-- The tone at index `k` has value `t`. -/
abbrev ToneHasValue (k : TierIdx) (t : TRN) : Prop :=
  (f.upper.get? k).map TierSpec.value = some t

/-! ### *FLOAT (Directional) -/

/-- `*FLOAT` (paper, eq. 16): one violation per tone not associated to a
    syllable. **Directional**: emits the indicator vector
    `floatIndicator`, with one entry per underlying tone position
    recording whether that tone is currently floating. -/
def starFloat : Constraint (FloatingForm S TRN) where
  name := "*FLOAT"
  family := .markedness
  eval := FloatingForm.floatIndicator
  order := .lex

/-- `*FLOAT (count)`: count-based variant of `starFloat`, emitting the *total*
    floating-tone count as a singleton `[count]` rather than a position-aware vector. -/
def starFloatCount : Constraint (FloatingForm S TRN) :=
  .ofCount "*FLOAT (count)" .markedness (fun f => f.floatIndicator.sum)

/-! ### *TAUTDOCK -/

/-- `*TAUTDOCK` (paper, eq. 15, after [wolf-2007]): one violation
    per GEN-inserted tautomorphic surface link. -/
def starTautDock : Constraint (FloatingForm S TRN) :=
  .ofCount "*TAUTDOCK" .markedness
    (fun f => (f.surfaceLinks.filter (fun l => f.IsInsertedLink l ∧ f.IsTautomorphic l)).card)

/-! ### *CROWD (per-morpheme tone count) -/

/-- The tone indices counting toward morpheme `m`'s tonal mass: surviving
    underlying tones of `m`, plus tones surface-linked to TBUs of `m`. -/
def tonesForMorpheme (m : Morpheme) : Finset TierIdx :=
  let ownAlive := (Finset.range f.upper.len).filter fun k =>
    f.IsAlive k ∧ f.upperMorpheme? k = some m
  let docked := (f.surfaceLinks.filter fun l => f.lowerMorpheme? l.snd = some m).image Prod.fst
  ownAlive ∪ docked

/-- `*CROWD` (paper eq. 5): one violation per morpheme with more than `threshold`
    tones (default 2), counting its surviving underlying tones plus tones docked onto
    its TBUs from other morphemes. -/
def starCrowd (threshold : Nat := 2) : Constraint (FloatingForm S TRN) :=
  .ofCount s!"*CROWD({threshold})" .markedness
    (fun f => (f.morphemes.filter (fun m => threshold < (tonesForMorpheme f m).card)).card)

/-! ### *FALL (falling contours on multi-linked TBUs) -/

/-- A tone pair `(t1, t2)` (in tier order) is **falling** iff it is HM, HL, or ML
    (paper eq. 23). -/
abbrev IsFallingPair (t1 t2 : TRN) : Prop :=
  (t1 = .H ∧ t2 = .M) ∨ (t1 = .H ∧ t2 = .L) ∨ (t1 = .M ∧ t2 = .L)

/-- A tone sequence contains a falling adjacent pair. -/
def HasFall : List TRN → Prop
  | []                  => False
  | [_]                 => False
  | t1 :: t2 :: rest    => IsFallingPair t1 t2 ∨ HasFall (t2 :: rest)

instance decidableHasFall : (ts : List TRN) → Decidable (HasFall ts)
  | []                  => isFalse not_false
  | [_]                 => isFalse not_false
  | t1 :: t2 :: rest    =>
    have : Decidable (HasFall (t2 :: rest)) := decidableHasFall (t2 :: rest)
    inferInstanceAs (Decidable (IsFallingPair t1 t2 ∨ HasFall (t2 :: rest)))

/-- `*FALL` (paper eq. 23): one violation per syllable with a falling contour
    (HM, HL, ML). -/
def starFall : Constraint (FloatingForm S TRN) :=
  .ofCount "*FALL" .markedness
    (fun f => f.countLower (fun i => HasFall (f.tierValues i)))

/-! ### *M<L (M-then-L adjacency on the tier) -/

/-- `*M<L` (paper eq. 29): one violation per M tone immediately preceding an L on the
    tonal tier — adjacency measured over the surviving (non-deleted) tones in `ulTier`
    order (deletions skip positions). -/
def starMlessL : Constraint (FloatingForm S TRN) :=
  .ofCount "*M<L" .markedness (fun f =>
    let aliveValues : List TRN :=
      f.aliveTierIdxs.filterMap (fun k => (f.upper.get? k).map TierSpec.value)
    (aliveValues.zip aliveValues.tail).countP (fun p => decide (p = (TRN.M, TRN.L))))

/-! ### HAVETONE -/

/-- `HAVETONE` (paper, eq. 17): one violation per syllable not
    associated to any tone. -/
def haveTone : Constraint (FloatingForm S TRN) :=
  .ofCount "HAVETONE" .markedness
    (fun f => f.countLower (fun i => (f.linksTo i).isEmpty = true))

/-! ### Faithfulness — Generic over Tone Value -/

/-- `MAX(T)` (paper, eq. 7c): one violation per underlying tone of
    value `t` deleted by GEN. -/
def maxTone (t : TRN) : Constraint (FloatingForm S TRN) :=
  .ofCount s!"MAX({reprStr t})" .faithfulness
    (fun f => f.countUpper (fun k => f.IsDeleted k ∧ ToneHasValue f k t))

/-- `DEP(link)/T` (paper, eq. 7a): one violation per surface link
    inserted by GEN whose linked tone has value `t`. -/
def depLinkTone (t : TRN) : Constraint (FloatingForm S TRN) :=
  .ofCount s!"DEP(link)/{reprStr t}" .faithfulness
    (fun f => (f.surfaceLinks.filter (fun l => f.IsInsertedLink l ∧ ToneHasValue f l.fst t)).card)

/-- `MAX(link)/T` (paper, eq. 7b): one violation per underlying link of
    value `t` deleted by GEN. -/
def maxLinkTone (t : TRN) : Constraint (FloatingForm S TRN) :=
  .ofCount s!"MAX(link)/{reprStr t}" .faithfulness
    (fun f => (f.links.filter (fun l => f.IsDeletedLink l ∧ ToneHasValue f l.fst t)).card)

/-- `INTEGRITY` ([mccarthy-prince-1995]; [akinbo-fwangwar-2026]): no input tone has
    multiple output correspondents — here, alive `ulTier` entries sharing tone value `t`
    and morpheme `m`. Spreading (one multi-linked entry) → 0; copying (`n` such entries)
    → `n - 1` violations. -/
def integrityTone (m : Morpheme) (t : TRN) :
    Constraint (FloatingForm S TRN) :=
  .ofCount s!"INTEGRITY-{reprStr t}({m.form})" .faithfulness
    (fun f => f.countUpper (fun k => f.IsAlive k ∧ f.upperMorpheme? k = some m ∧ ToneHasValue f k t) - 1)

end Tone
