/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
module

public import Linglib.Phonology.Autosegmental.Floating
public import Linglib.Phonology.Tone.Basic
public import Linglib.Phonology.Constraints.Defs

/-!
# Tonal constraints

OT/HS constraint constructors over the candidates `Candidate u` of an autosegmental form
`u : Form S TRN M` (`Phonology/Autosegmental/Floating.lean`), generic over the segment type
`S` and the opaque sponsor type `M`. Each is a canonical `Constraints.Constraint`, a scalar
`· → ℕ` violation count. Equation numbers below are [mcpherson-lamont-2026]'s.

## Main definitions

* `starFloatBlock` / `starFloatBlockRev` / `starFloatCount` — `*FLOAT` (eq. 16):
  directional block (L→R / R→L) vs. count variant
* `starTautDock` — `*TAUTDOCK` (eq. 15, after [wolf-2007])
* `starCrowd` — `*CROWD` (eq. 5): per-morpheme tone-count ceiling
* `starFall` — `*FALL` (eq. 23): falling-contour ban
* `starMlessL` — `*M<L` (eq. 29): M immediately before L on the tier
* `maxTone` / `depLinkTone` / `maxLinkTone` — `MAX(T)` / `DEP(link)/T` / `MAX(link)/T` (eq. 7)
* `haveTone` — `HAVETONE` (eq. 17)
* `integrityTone` — `INTEGRITY` ([akinbo-fwangwar-2026]; [mccarthy-prince-1995])
* `leftAnchorTone` / `rightAnchorTone` — morpheme-specific `ANCHOR` ([finley-2009];
  [akinbo-fwangwar-2026])

## Implementation notes

Faithfulness (`maxTone`, `maxLinkTone`, `depLinkTone`) compares a candidate's surface state
with its form, which the candidate carries as a parameter. Without that underlying-form
tracking, faithfulness can't fire and the [mcpherson-lamont-2026] LR-vs-RL multi-step
asymmetry collapses.

Directionality is **not** a separate kind of constraint. Following [lamont-2022b]
(directionality is a property of EVAL), `*FLOAT` is a position-indexed *block* of
scalar float-flag constraints (`starFloatBlock`), whose coordinate `i` flags whether
autosegment `i` is floating, so splicing the block into a ranking and comparing under the
canonical lexicographic profile order recovers the directional EVAL exactly
(`Core.Optimization.Evaluation.lexLE_ofFn`). The block is laid out left-to-right for
`*FLOAT^→` (`starFloatBlock`) or right-to-left for `*FLOAT^←` (`starFloatBlockRev`);
`starFloatCount` is the count collapse (parallel `*FLOAT`). They agree on at most one
floating tone but diverge as the set grows — a single count cannot tell "delete
leftmost" from "delete rightmost" ([mcpherson-lamont-2026]'s eq. (62) divergent tie).
-/

@[expose] public section

namespace Tone

open Autosegmental
open Tone (TRN)
open Constraints

variable {S M : Type*} [DecidableEq S] [DecidableEq M] {u : Form S TRN M}

/-! ### Tone-value predicate

Link faithfulness (`Candidate.insertedLinks` / `deletedLinks`) and the morphemes
(`Form.morphemes`, `Form.lowerOfMorpheme`) are tone-agnostic and live on the substrate; only
the `TRN`-reading predicate is here. -/

/-- The tone at index `k` has value `t`. -/
abbrev ToneHasValue (k : Fin u.upper.len) (t : TRN) : Prop := (u.upper.label k).value = t

/-! ### *FLOAT (Directional) -/

/-- `*FLOAT` (paper, eq. 16) is a position-indexed block of scalar constraints, whose
    coordinate `i` flags whether underlying tone `i` is currently floating. Spliced forward it
    is `*FLOAT^→`, and the directional EVAL is recovered as the canonical lex order over the
    block ([lamont-2022b]). -/
def starFloatBlock : List (Constraint (Candidate u)) :=
  (List.finRange u.upper.len).map fun i c ↦ if c.IsFloating i then 1 else 0

/-- `*FLOAT^←` is `starFloatBlock` laid out in reverse position order, for right-to-left
    evaluation. -/
def starFloatBlockRev : List (Constraint (Candidate u)) := starFloatBlock.reverse

/-- The count variant of `*FLOAT` totals the floating tones as a single scalar constraint,
    the degree collapse of `starFloatBlock`. -/
def starFloatCount : Constraint (Candidate u) :=
  fun c ↦ (Finset.univ.filter c.IsFloating).card

/-! ### *TAUTDOCK -/

/-- `*TAUTDOCK` (paper, eq. 15, after [wolf-2007]) assigns one violation per GEN-inserted
    tautomorphemic surface link. -/
def starTautDock : Constraint (Candidate u) :=
  fun c ↦ (c.insertedLinks.filter u.IsTautomorphemic).card

/-! ### *CROWD (per-morpheme tone count) -/

/-- The tones counting toward morpheme `m`'s tonal mass are its surviving underlying tones
    and the tones surface-linked to its TBUs. -/
def tonesForMorpheme (c : Candidate u) (m : M) : Finset (Fin u.upper.len) :=
  (Finset.univ.filter fun k ↦ k ∉ c.deleted ∧ (u.upper.label k).morpheme = m) ∪
    (c.links.filter fun l ↦ (u.lower.label l.2).morpheme = m).image Prod.fst

/-- `*CROWD` (paper eq. 5) assigns one violation per morpheme with more than `threshold`
    tones (default 2), counting its surviving underlying tones plus tones docked onto its
    TBUs from other morphemes. -/
def starCrowd (threshold : Nat := 2) : Constraint (Candidate u) :=
  fun c ↦ (u.morphemes.filter fun m ↦ threshold < (tonesForMorpheme c m).card).card

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

/-- `*FALL` (paper eq. 23) assigns one violation per syllable with a falling contour (HM,
    HL, ML). -/
def starFall : Constraint (Candidate u) :=
  fun c ↦ (Finset.univ.filter fun i ↦ HasFall (c.tierValues i)).card

/-! ### *M<L (M-then-L adjacency on the tier) -/

/-- `*M<L` (paper eq. 29) assigns one violation per M tone immediately preceding an L on
    the tonal tier, with adjacency measured over the surviving tones in tier order, so
    deletions skip positions. -/
def starMlessL : Constraint (Candidate u) :=
  fun c ↦
    let aliveValues : List TRN := c.alive.map fun k ↦ (u.upper.label k).value
    (aliveValues.zip aliveValues.tail).countP (fun p ↦ decide (p = (TRN.M, TRN.L)))

/-! ### HAVETONE -/

/-- `HAVETONE` (paper, eq. 17) assigns one violation per syllable not associated to any
    tone. -/
def haveTone : Constraint (Candidate u) :=
  fun c ↦ (Finset.univ.filter fun i ↦ c.linksTo i = []).card

/-! ### Faithfulness — Generic over Tone Value -/

/-- `MAX(T)` (paper, eq. 7c) assigns one violation per underlying tone of value `t` deleted
    by GEN. -/
def maxTone (t : TRN) : Constraint (Candidate u) :=
  fun c ↦ (c.deleted.filter fun k ↦ ToneHasValue k t).card

/-- `DEP(link)/T` (paper, eq. 7a) assigns one violation per surface link inserted by GEN
    whose linked tone has value `t`. -/
def depLinkTone (t : TRN) : Constraint (Candidate u) :=
  fun c ↦ (c.insertedLinks.filter fun l ↦ ToneHasValue l.1 t).card

/-- `MAX(link)/T` (paper, eq. 7b) assigns one violation per underlying link of value `t`
    deleted by GEN. -/
def maxLinkTone (t : TRN) : Constraint (Candidate u) :=
  fun c ↦ (c.deletedLinks.filter fun l ↦ ToneHasValue l.1 t).card

/-- `INTEGRITY` ([mccarthy-prince-1995]; [akinbo-fwangwar-2026]) forbids an input tone from
    having several output correspondents. It counts the alive tier entries sharing tone value
    `t` and morpheme `m` beyond the first, so spreading by one multi-linked entry costs
    nothing and copying into `n` entries costs `n - 1`. -/
def integrityTone (m : M) (t : TRN) : Constraint (Candidate u) :=
  fun c ↦
    (Finset.univ.filter fun k ↦
      k ∉ c.deleted ∧ (u.upper.label k).morpheme = m ∧ ToneHasValue k t).card - 1

/-! ### Morpheme-specific anchoring
[finley-2009]

A grammatical tone sponsored by morpheme `m` must correspond to an edge of a host root. With
several hosts the constraint counts the host it is realised on that is closest to satisfying
it; unrealised anywhere, it counts every TBU of every host ([akinbo-fwangwar-2026] (22),
(26)). -/

/-- Backbone position `i` bears an upper-tier element of value `t` sponsored by `m`. -/
def bearsTone (c : Candidate u) (m : M) (t : TRN) (i : Fin u.lower.len) : Bool :=
  (c.linksTo i).any fun k ↦ decide ((u.upper.label k).value = t ∧ (u.upper.label k).morpheme = m)

/-- `LEFT-ANCHOR-T_m` counts the TBUs between a host's left edge and the leftmost TBU
bearing `t` from `m`, the fewest over the hosts bearing it, or every TBU of every host if none
does. -/
def leftAnchorTone (m : M) (t : TRN) (hosts : List M) : Constraint (Candidate u) :=
  fun c ↦
    match (hosts.filterMap fun h ↦ (u.lowerOfMorpheme h).findIdx? (bearsTone c m t)).min? with
    | some d => d
    | none => (hosts.map fun h ↦ (u.lowerOfMorpheme h).length).sum

/-- `RIGHT-ANCHOR-T_m` counts as `leftAnchorTone` does, from the host's right edge. -/
def rightAnchorTone (m : M) (t : TRN) (hosts : List M) : Constraint (Candidate u) :=
  fun c ↦
    match (hosts.filterMap fun h ↦
        (u.lowerOfMorpheme h).reverse.findIdx? (bearsTone c m t)).min? with
    | some d => d
    | none => (hosts.map fun h ↦ (u.lowerOfMorpheme h).length).sum

end Tone
