import Linglib.Theories.Phonology.Autosegmental.Floating
import Linglib.Core.Constraint.OT.DirectionalTableau

/-!
# Tonal Constraints — Generic Constructors over `FloatingForm`
@cite{wolf-2007} @cite{cahill-2004} @cite{mcpherson-lamont-2026}

OT/HS constraint constructors over the `FloatingForm S` autosegmental
representation (`Theories/Phonology/Autosegmental/Floating.lean`).
Generic over the segment type `S`.

All constraints are `DirectionalConstraint`s:
- Genuinely directional (e.g., `*FLOAT^→`) emit indicator vectors with
  positions in tier order.
- Parallel-by-nature emit singletons `[count]` (per `EvalMode.le_singleton`'s
  singleton-degeneracy guarantee).

## Constraint inventory (paper, eqs. 5, 7, 15-17, 23)

- `starFloat`           ← paper eq. 16 (`*FLOAT`, directional)
- `starTautDock`        ← paper eq. 15 (`*TAUTDOCK`, after @cite{wolf-2007})
- `starCrowd threshold` ← paper eq. 5 (`*CROWD`, after @cite{cahill-2004})
- `starFall`            ← paper eq. 23 (`*FALL`, falling-contour ban)
- `maxTone t`           ← paper eq. 7c (`MAX(T)`)
- `depLinkTone t`       ← paper eq. 7a (`DEP(link)/T`)
- `maxLinkTone t`       ← paper eq. 7b (`MAX(link)/T`)
- `haveTone`            ← paper eq. 17 (`HAVETONE`)

## Faithfulness against the underlying form

Faithfulness constraints (`maxTone`, `maxLinkTone`, `depLinkTone`)
compare surface state to the immutable underlying state stored in
`FloatingForm`. This is what makes the @cite{mcpherson-lamont-2026}
fig. 3 multi-step asymmetry visible: without underlying-form tracking,
faithfulness can't fire and the LR-vs-RL distinction collapses.
-/

namespace Phonology.Tone

open Phonology.Autosegmental
open Phonology.Autosegmental.RegisterTier (TRN)
open Core.Constraint.OT (DirectionalConstraint ConstraintFamily)

variable {S : Type} [DecidableEq S]

-- ============================================================================
-- § 1: Predicate Helpers
-- ============================================================================

/-- The link `(k, i)` is tautomorphic: its tone and TBU share a morpheme.
    Both indices must resolve to options (out-of-range = no match). -/
def IsTautomorphic (f : FloatingForm S) (l : Link) : Prop :=
  (f.ulTones[l.fst]?).map ToneSpec.morpheme =
    (f.segs[l.snd]?).map SegSpec.morpheme ∧
  (f.ulTones[l.fst]?).isSome

instance (f : FloatingForm S) (l : Link) : Decidable (IsTautomorphic f l) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The link `(k, i)` was inserted by GEN (in surface but not in underlying). -/
def IsInsertedLink (f : FloatingForm S) (l : Link) : Prop :=
  l ∈ f.surfaceLinks ∧ l ∉ f.ulLinks

instance (f : FloatingForm S) (l : Link) : Decidable (IsInsertedLink f l) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The link `(k, i)` was deleted by GEN (in underlying but not in surface). -/
def IsDeletedLink (f : FloatingForm S) (l : Link) : Prop :=
  l ∈ f.ulLinks ∧ l ∉ f.surfaceLinks

instance (f : FloatingForm S) (l : Link) : Decidable (IsDeletedLink f l) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The tone at index `k` has value `t`. -/
def ToneHasValue (f : FloatingForm S) (k : ToneIdx) (t : TRN) : Prop :=
  (f.ulTones[k]?).map ToneSpec.tone = some t

instance (f : FloatingForm S) (k : ToneIdx) (t : TRN) : Decidable (ToneHasValue f k t) :=
  inferInstanceAs (Decidable (_ = _))

-- ============================================================================
-- § 2: *FLOAT (Directional)
-- ============================================================================

/-- `*FLOAT` (paper, eq. 16): one violation per tone not associated to a
    syllable. **Directional**: emits the indicator vector
    `floatIndicator`, with one entry per underlying tone position
    recording whether that tone is currently floating. -/
def starFloat : DirectionalConstraint (FloatingForm S) where
  name := "*FLOAT"
  family := .markedness
  eval := FloatingForm.floatIndicator

-- ============================================================================
-- § 3: *TAUTDOCK
-- ============================================================================

/-- `*TAUTDOCK` (paper, eq. 15, after @cite{wolf-2007}): one violation
    per GEN-inserted tautomorphic surface link. -/
def starTautDock : DirectionalConstraint (FloatingForm S) where
  name := "*TAUTDOCK"
  family := .markedness
  eval := fun f =>
    [(f.surfaceLinks.filter (fun l => IsInsertedLink f l ∧ IsTautomorphic f l)).card]

-- ============================================================================
-- § 4: *CROWD (per-morpheme tone count)
-- ============================================================================

/-- The tone at index `k` belongs to morpheme `m`. -/
def ToneInMorpheme (f : FloatingForm S) (k : ToneIdx) (m : MorphemeId) : Prop :=
  (f.ulTones[k]?).map ToneSpec.morpheme = some m

instance (f : FloatingForm S) (k : ToneIdx) (m : MorphemeId) :
    Decidable (ToneInMorpheme f k m) :=
  inferInstanceAs (Decidable (_ = _))

/-- The TBU at index `i` belongs to morpheme `m`. -/
def SegInMorpheme (f : FloatingForm S) (i : SegIdx) (m : MorphemeId) : Prop :=
  (f.segs[i]?).map SegSpec.morpheme = some m

instance (f : FloatingForm S) (i : SegIdx) (m : MorphemeId) :
    Decidable (SegInMorpheme f i m) :=
  inferInstanceAs (Decidable (_ = _))

/-- The set of tone indices counting toward morpheme `m`'s tonal mass:
    surviving underlying tones of `m`, plus tones surface-linked to
    TBUs of `m`. -/
def tonesForMorpheme (f : FloatingForm S) (m : MorphemeId) : Finset ToneIdx :=
  let ownAlive := (Finset.range f.ulTones.length).filter fun k =>
    f.IsAlive k ∧ ToneInMorpheme f k m
  let docked := (f.surfaceLinks.filter fun l => SegInMorpheme f l.snd m).image Prod.fst
  ownAlive ∪ docked

/-- `*CROWD` (paper, eq. 5, after @cite{cahill-2004}): one violation per
    morpheme associated with more than `threshold` tones. Default
    `threshold = 2` matches the paper.

    Counting includes surviving underlying tones of the morpheme PLUS
    surface tones from other morphemes docked onto this morpheme's
    TBUs. This is how the paper (p. 32) blocks rightward docking onto
    `/rī^H/`: rī already has 2 tones (M + own H), so an external H
    docking would make 3. -/
def starCrowd (threshold : Nat := 2) : DirectionalConstraint (FloatingForm S) where
  name := s!"*CROWD({threshold})"
  family := .markedness
  eval := fun f =>
    let morphIds : Finset MorphemeId :=
      (f.segs.map SegSpec.morpheme).toFinset ∪
      (f.ulTones.map ToneSpec.morpheme).toFinset
    [(morphIds.filter (fun m => (tonesForMorpheme f m).card > threshold)).card]

-- ============================================================================
-- § 5: *FALL (falling contours on multi-linked TBUs)
-- ============================================================================

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
    order (via `toneSequence`) and scanning for falling adjacent pairs.
    Uses `List.range` + `countP` rather than `Finset.range` + `filter`
    + `card` so kernel `decide` reduces. -/
def starFall : DirectionalConstraint (FloatingForm S) where
  name := "*FALL"
  family := .markedness
  eval := fun f =>
    [(List.range f.segs.length).countP (fun i => decide (HasFall (f.toneSequence i)))]

-- ============================================================================
-- § 6: HAVETONE
-- ============================================================================

/-- `HAVETONE` (paper, eq. 17): one violation per syllable not
    associated to any tone. -/
def haveTone : DirectionalConstraint (FloatingForm S) where
  name := "HAVETONE"
  family := .markedness
  eval := fun f =>
    [(List.range f.segs.length).countP (fun i => (f.linksTo i).isEmpty)]

-- ============================================================================
-- § 7: Faithfulness — Generic over Tone Value
-- ============================================================================

/-- `MAX(T)` (paper, eq. 7c): one violation per underlying tone of
    value `t` deleted by GEN. -/
def maxTone (t : TRN) : DirectionalConstraint (FloatingForm S) where
  name := s!"MAX({reprStr t})"
  family := .faithfulness
  eval := fun f =>
    [(List.range f.ulTones.length).countP
      (fun k => decide (f.IsDeleted k ∧ ToneHasValue f k t))]

/-- `DEP(link)/T` (paper, eq. 7a): one violation per surface link
    inserted by GEN whose linked tone has value `t`. -/
def depLinkTone (t : TRN) : DirectionalConstraint (FloatingForm S) where
  name := s!"DEP(link)/{reprStr t}"
  family := .faithfulness
  eval := fun f =>
    [(f.surfaceLinks.filter (fun l => IsInsertedLink f l ∧ ToneHasValue f l.fst t)).card]

/-- `MAX(link)/T` (paper, eq. 7b): one violation per underlying link of
    value `t` deleted by GEN. -/
def maxLinkTone (t : TRN) : DirectionalConstraint (FloatingForm S) where
  name := s!"MAX(link)/{reprStr t}"
  family := .faithfulness
  eval := fun f =>
    [(f.ulLinks.filter (fun l => IsDeletedLink f l ∧ ToneHasValue f l.fst t)).card]

end Phonology.Tone
