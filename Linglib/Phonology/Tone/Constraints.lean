import Linglib.Phonology.Autosegmental.Floating
import Linglib.Phonology.OptimalityTheory.DirectionalTableau

/-!
# Tonal constraints

OT/HS constraint constructors over the `FloatingForm S TRN` autosegmental
representation (`Phonology/Autosegmental/Floating.lean`), generic over the segment
type `S`. Each is a `DirectionalConstraint`: genuinely directional ones (e.g.
`*FLOAT^→`) emit indicator vectors with positions in tier order, while
parallel-by-nature ones emit singletons `[count]` (per `EvalMode.le_singleton`'s
singleton-degeneracy guarantee). Equation numbers below are [mcpherson-lamont-2026]'s.

## Main definitions

* `starFloat` / `starFloatCount` — `*FLOAT` (eq. 16): position-aware indicator vs. count variant
* `starTautDock` — `*TAUTDOCK` (eq. 15, after [wolf-2007])
* `starCrowd` — `*CROWD` (eq. 5): per-morpheme tone-count ceiling
* `starFall` — `*FALL` (eq. 23): falling-contour ban
* `starMlessL` — `*M<L` (eq. 29): M immediately before L on the tier
* `maxTone` / `depLinkTone` / `maxLinkTone` — `MAX(T)` / `DEP(link)/T` / `MAX(link)/T` (eq. 7)
* `haveTone` — `HAVETONE` (eq. 17)
* `integrityTone` — `INTEGRITY` ([akinbo-fwangwar-2026]; [mcpherson-prince-1995])

## Implementation notes

Faithfulness (`maxTone`, `maxLinkTone`, `depLinkTone`) compares surface state to the
immutable underlying state stored in `FloatingForm`. Without that underlying-form
tracking, faithfulness can't fire and the [mcpherson-lamont-2026] LR-vs-RL multi-step
asymmetry collapses.

`starFloat` (a position-aware indicator vector) and `starFloatCount` (the total count)
agree with at most one floating tone but diverge as the set grows: count comparison
cannot tell "delete leftmost" from "delete rightmost" — [mcpherson-lamont-2026]'s
eq. (62) divergent tie. So the parallel-vs-directional split lives in the *constraint*
(count vs. indicator), not the EVAL mode: `EvalMode.le .parallel` and
`EvalMode.le (.directional .leftToRight)` both apply the same `LexLE`; the flag documents
intent and selects vector reversal for the right-to-left case.
-/

namespace Phonology.Tone

open Phonology.Autosegmental
open Phonology.Autosegmental.RegisterTier (TRN)
open Constraint OptimalityTheory

variable {S : Type*} [DecidableEq S] (f : FloatingForm S TRN)

/-! ### Predicate Helpers -/

/-- The link `(k, i)` was inserted by GEN (in surface but not in underlying). -/
def IsInsertedLink (l : Link) : Prop :=
  l ∈ f.surfaceLinks ∧ l ∉ f.links

instance (l : Link) : Decidable (IsInsertedLink f l) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The link `(k, i)` was deleted by GEN (in underlying but not in surface). -/
def IsDeletedLink (l : Link) : Prop :=
  l ∈ f.links ∧ l ∉ f.surfaceLinks

instance (l : Link) : Decidable (IsDeletedLink f l) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The tone at index `k` has value `t`. -/
def ToneHasValue (k : TierIdx) (t : TRN) : Prop :=
  (f.upper[k]?).map TierSpec.value = some t

instance (k : TierIdx) (t : TRN) : Decidable (ToneHasValue f k t) :=
  inferInstanceAs (Decidable (_ = _))

/-! ### *FLOAT (Directional) -/

/-- `*FLOAT` (paper, eq. 16): one violation per tone not associated to a
    syllable. **Directional**: emits the indicator vector
    `floatIndicator`, with one entry per underlying tone position
    recording whether that tone is currently floating. -/
def starFloat : DirectionalConstraint (FloatingForm S TRN) where
  name := "*FLOAT"
  family := .markedness
  eval := FloatingForm.floatIndicator

/-- `*FLOAT (count)`: count-based variant of `starFloat`, emitting the *total*
    floating-tone count as a singleton `[count]` rather than a position-aware vector. -/
def starFloatCount : DirectionalConstraint (FloatingForm S TRN) where
  name := "*FLOAT (count)"
  family := .markedness
  eval := fun f => [f.floatIndicator.sum]

/-! ### *TAUTDOCK -/

/-- `*TAUTDOCK` (paper, eq. 15, after [wolf-2007]): one violation
    per GEN-inserted tautomorphic surface link. -/
def starTautDock : DirectionalConstraint (FloatingForm S TRN) where
  name := "*TAUTDOCK"
  family := .markedness
  eval := fun f =>
    [(f.surfaceLinks.filter (fun l => IsInsertedLink f l ∧ f.IsTautomorphic l)).card]

/-! ### *CROWD (per-morpheme tone count) -/

/-- The tone at index `k` belongs to morpheme `m`. -/
def ToneInMorpheme (k : TierIdx) (m : Morpheme) : Prop :=
  (f.upper[k]?).map TierSpec.morpheme = some m

instance (k : TierIdx) (m : Morpheme) :
    Decidable (ToneInMorpheme f k m) :=
  inferInstanceAs (Decidable (_ = _))

/-- The TBU at index `i` belongs to morpheme `m`. -/
def SegInMorpheme (i : SegIdx) (m : Morpheme) : Prop :=
  (f.lower[i]?).map SegSpec.morpheme = some m

instance (i : SegIdx) (m : Morpheme) :
    Decidable (SegInMorpheme f i m) :=
  inferInstanceAs (Decidable (_ = _))

/-- The set of tone indices counting toward morpheme `m`'s tonal mass:
    surviving underlying tones of `m`, plus tones surface-linked to
    TBUs of `m`. -/
def tonesForMorpheme (m : Morpheme) : Finset TierIdx :=
  let ownAlive := (Finset.range f.upper.length).filter fun k =>
    f.IsAlive k ∧ ToneInMorpheme f k m
  let docked := (f.surfaceLinks.filter fun l => SegInMorpheme f l.snd m).image Prod.fst
  ownAlive ∪ docked

/-- `*CROWD` (paper eq. 5): one violation per morpheme with more than `threshold`
    tones (default 2), counting its surviving underlying tones plus tones docked onto
    its TBUs from other morphemes. -/
def starCrowd (threshold : Nat := 2) : DirectionalConstraint (FloatingForm S TRN) where
  name := s!"*CROWD({threshold})"
  family := .markedness
  eval := fun f =>
    let morphIds : Finset Morpheme :=
      (f.lower.map SegSpec.morpheme).toFinset ∪
      (f.upper.map TierSpec.morpheme).toFinset
    [(morphIds.filter (fun m => (tonesForMorpheme f m).card > threshold)).card]

/-! ### *FALL (falling contours on multi-linked TBUs) -/

/-- A tone pair `(t1, t2)` (in tier order) is **falling** iff it is
    HM, HL, or ML (paper, eq. 23). TRN's `H`, `M`, `L` are not
    constructors (they're `def`s), so we use equality rather than
    pattern matching. -/
def IsFallingPair (t1 t2 : TRN) : Prop :=
  (t1 = .H ∧ t2 = .M) ∨ (t1 = .H ∧ t2 = .L) ∨ (t1 = .M ∧ t2 = .L)

instance (t1 t2 : TRN) : Decidable (IsFallingPair t1 t2) :=
  inferInstanceAs (Decidable (_ ∨ _))

/-- A tone sequence contains a falling adjacent pair. Recursive
    Prop predicate; the explicit decidability instance below carries
    the recursion through. -/
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

/-- `*FALL` (paper, eq. 23): one violation per syllable associated with
    a falling contour (HM, HL, ML).

    A TBU is checked by extracting its surface-linked tones in tier
    order (via `tierValues`) and scanning for falling adjacent pairs.
    Uses `List.range` + `countP` rather than `Finset.range` + `filter`
    + `card` so kernel `decide` reduces. -/
def starFall : DirectionalConstraint (FloatingForm S TRN) where
  name := "*FALL"
  family := .markedness
  eval := fun f =>
    [(List.range f.lower.length).countP (fun i => decide (HasFall (f.tierValues i)))]

/-! ### *M<L (M-then-L adjacency on the tier) -/

/-- `*M<L` (paper, eq. 29): one violation per M tone that immediately
    precedes an L tone on the tonal tier. The "tier" is the sequence
    of surviving (non-deleted) underlying tones in `ulTier` order;
    deletions skip positions, so adjacency is measured over the alive
    subsequence.

    Motivates [mcpherson-lamont-2026]'s account of why floating
    H tones can dock leftward tautomorphically before L (eq. 30):
    without `*M<L ≫ *TAUTDOCK`, an underlying /M H L/ sequence would
    prefer H deletion, but that yields a surface ML adjacency which
    *M<L penalises. Tautomorphic docking of H breaks the ML adjacency,
    creating an MH contour rather than M-L. -/
def starMlessL : DirectionalConstraint (FloatingForm S TRN) where
  name := "*M<L"
  family := .markedness
  eval := fun f =>
    let aliveValues : List TRN :=
      f.aliveTierIdxs.filterMap fun k => (f.upper[k]?).map TierSpec.value
    [aliveValues.zip aliveValues.tail
      |>.countP fun p => decide (p.1 = TRN.M ∧ p.2 = TRN.L)]

/-! ### HAVETONE -/

/-- `HAVETONE` (paper, eq. 17): one violation per syllable not
    associated to any tone. -/
def haveTone : DirectionalConstraint (FloatingForm S TRN) where
  name := "HAVETONE"
  family := .markedness
  eval := fun f =>
    [(List.range f.lower.length).countP (fun i => (f.linksTo i).isEmpty)]

/-! ### Faithfulness — Generic over Tone Value -/

/-- `MAX(T)` (paper, eq. 7c): one violation per underlying tone of
    value `t` deleted by GEN. -/
def maxTone (t : TRN) : DirectionalConstraint (FloatingForm S TRN) where
  name := s!"MAX({reprStr t})"
  family := .faithfulness
  eval := fun f =>
    [(List.range f.upper.length).countP
      (fun k => decide (f.IsDeleted k ∧ ToneHasValue f k t))]

/-- `DEP(link)/T` (paper, eq. 7a): one violation per surface link
    inserted by GEN whose linked tone has value `t`. -/
def depLinkTone (t : TRN) : DirectionalConstraint (FloatingForm S TRN) where
  name := s!"DEP(link)/{reprStr t}"
  family := .faithfulness
  eval := fun f =>
    [(f.surfaceLinks.filter (fun l => IsInsertedLink f l ∧ ToneHasValue f l.fst t)).card]

/-- `MAX(link)/T` (paper, eq. 7b): one violation per underlying link of
    value `t` deleted by GEN. -/
def maxLinkTone (t : TRN) : DirectionalConstraint (FloatingForm S TRN) where
  name := s!"MAX(link)/{reprStr t}"
  family := .faithfulness
  eval := fun f =>
    [(f.links.filter (fun l => IsDeletedLink f l ∧ ToneHasValue f l.fst t)).card]

/-- `INTEGRITY` (paper, [mccarthy-prince-1995]; [akinbo-fwangwar-2026]
    eq. 22c): no input tone has multiple output correspondents. In our
    autosegmental encoding, an "output correspondent of an input tone"
    is an alive ulTier entry sharing the input tone's value AND
    morpheme. SPREADING (one alive ulTier entry, multi-linked) → 0
    violations. COPYING (multiple alive ulTier entries with same
    value+morpheme) → `(count - 1)` violations.

    Parameterised by the morpheme `m` and tone value `t` whose copies
    are being counted (typically the verbaliser's M or H). The paper's
    INTEGRITY-Mᵥ is `integrityTone vbzMorph .M`. -/
def integrityTone (m : Morpheme) (t : TRN) :
    DirectionalConstraint (FloatingForm S TRN) where
  name := s!"INTEGRITY-{reprStr t}({m.form})"
  family := .faithfulness
  eval := fun f =>
    let aliveCopies := (List.range f.upper.length).countP fun k =>
      decide (f.IsAlive k ∧ ToneInMorpheme f k m ∧ ToneHasValue f k t)
    [if aliveCopies = 0 then 0 else aliveCopies - 1]

end Phonology.Tone
