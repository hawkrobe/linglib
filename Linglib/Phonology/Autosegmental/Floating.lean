import Linglib.Morphology.MorphWord
import Linglib.Phonology.Autosegmental.Graph
import Linglib.Phonology.Autosegmental.GrammaticalTone
import Linglib.Phonology.Autosegmental.NoCrossing
import Linglib.Phonology.Autosegmental.RegisterTier
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod

/-!
# Floating autosegmental form (Goldsmith)

Goldsmith-style autosegmental representation: tier elements (tones,
floating segments, features) sit on a tier above the segmental backbone,
connected by **association lines** (links). Multiple tier elements can
associate to one backbone position (forming contours); a tier element
with no associations is **floating**. Generic over both backbone type
`S` (the lower tier) and tier-value type `T` (the upper tier); tonal use
instantiates `T := TRN`, while non-tonal autosegmental work
([laoide-kemp-2026]'s floating consonants, [lieber-1983]'s
floating features) chooses other `T` values.

## Main definitions

* `Link` — an autosegmental link `(tier-index, backbone-index)`.
* `TierSpec T`, `SegSpec S` — tier and backbone elements carrying
  morpheme membership via `Morphology.WordStructure.Morpheme`
  (re-exported into this namespace).
* `FloatingForm S T` — autosegmental form with underlying/surface
  split.
* `FloatingForm.IsAlive`, `IsLinked`, `IsFloating`, `IsTautomorphic`,
  `Crosses` — decidable predicates on tier elements and links.
* `FloatingForm.deleteTierElem`, `insertLink`, `deleteLink` — atomic
  GEN operations (paper subset).
* `FloatingForm.gen` — one-step GEN as a `Finset` of candidate forms.
* `FloatingForm.floatIndicator`, `linksTo`, `tierValues` — indicator
  vectors for constraint evaluation.

## Implementation notes

The form carries an immutable **underlying** state (`segs`, `ulTier`,
`ulLinks`) and a mutable **surface** state (`deletedTier`,
`surfaceLinks`). GEN operations modify only the surface state. A
tier element is **floating** iff it is not deleted and no surface
link references it.

The refactor over the prior overwrite-semantics encoding
(`GrammaticalTone.tonalOverwrite`) is required by
[mcpherson-lamont-2026]: *CROWD penalises backbone positions
with too many associated tier elements, and *FALL penalises HM/HL/ML
contours — both of which presuppose multi-element-per-position
representation.

A surface link `(k, i)` is **tautomorphic** iff
`upper[k].morpheme = lower[i].morpheme`. *TAUTDOCK (after
[wolf-2007]) penalises tautomorphic links inserted by GEN.

`gen` implements a paper-subset of operations: delete tier element,
insert link, delete link. Insert-and-associate and shift operations
are omitted (not needed for the fig. 3 derivation in the source
paper). The no-crossing filter inside GEN enforces autosegmental
well-formedness ([goldsmith-1976]).

## References

* [goldsmith-1976] — autosegmental phonology, no-crossing constraint
* [wolf-2007] — *TAUTDOCK
* [mcpherson-lamont-2026] — grammatical tone with multi-tone TBUs
* [laoide-kemp-2026] — non-tonal floating segments (Irish ICM)
* [lieber-1983] — floating features in autosegmental morphology
-/

namespace Phonology.Autosegmental

open Phonology.Autosegmental.RegisterTier (TRN)

-- Re-export `Morpheme` so autosegmental consumers see it unqualified
-- after `open Phonology.Autosegmental`.
export Morphology.WordStructure (Morpheme)

/-! ### Tier and link primitives -/

/-- Index into the upper tier. -/
abbrev TierIdx := Nat

/-- Index into the lower tier. -/
abbrev SegIdx := Nat

/-- An autosegmental link: tier element `fst` is associated to
    backbone-position `snd`. -/
abbrev Link := TierIdx × SegIdx

/-- An autosegmental tier element: a value of type `T` plus morpheme
    membership. Generalises [goldsmith-1976]'s tonal-tier element
    to arbitrary tier-value types (tones, segments, features). -/
structure TierSpec (T : Type*) where
  /-- The tier value (tone, segment, feature, ...). -/
  value : T
  morpheme : Morpheme
  deriving DecidableEq, Repr

/-- A segmental backbone element: segment plus morpheme membership.
    Generic over the segment type `S`. -/
structure SegSpec (S : Type*) where
  seg : S
  morpheme : Morpheme
  deriving DecidableEq, Repr

/-! ### `FloatingForm`

`FloatingForm S T` is an autosegmental form with segmental backbone
of type `S` and tier-value type `T`. Tonal use chooses `T := TRN`;
non-tonal autosegmental work chooses other `T` values
([laoide-kemp-2026], [lieber-1983]). The OT-style
bookkeeping (`deletedTier`, `surfaceLinks` vs underlying `links`) is
language-independent.
-/

/-- An autosegmental form: extends `Graph (TierSpec T) (SegSpec S)`
    with OT-style surface bookkeeping. The inherited `Graph` is the
    *underlying* representation; `deletedTier` and `surfaceLinks`
    track the surface state separately. -/
structure FloatingForm (S T : Type*)
    extends Graph (TierSpec T) (SegSpec S) where
  /-- SURFACE deletion set on the upper tier (current state). -/
  deletedTier : Finset TierIdx
  /-- SURFACE association lines (current state). May differ from
      the inherited `links` (the underlying associations). -/
  surfaceLinks : Finset Link
  deriving DecidableEq


/-- Hides the `Finset` fields (mathlib's `Finset.Repr` is `unsafe`) and
    prints only segments and underlying tier elements; debug-only. -/
instance {S T : Type*} [Repr S] [Repr T] : Repr (FloatingForm S T) where
  reprPrec f _ :=
    f!"⟨lower={repr (f.lower.map SegSpec.seg)}, upper={repr f.upper}⟩"

namespace FloatingForm

variable {S T : Type*} [DecidableEq S] [DecidableEq T]

/-! ### Surface graph (derived view) -/

/-- The **surface graph**: same tiers as the underlying graph but with
    `surfaceLinks` in place of `links`. Makes the underlying/surface
    duality explicit — both states are `Graph`s sharing tier data. -/
@[reducible] def surfaceGraph (f : FloatingForm S T) :
    Graph (TierSpec T) (SegSpec S) :=
  { f.toGraph with links := f.surfaceLinks }

/-! ### Construction -/

/-- Construct an input form: surface state mirrors underlying state,
    nothing deleted, all underlying links intact. -/
def mkInput (lower : List (SegSpec S)) (upper : List (TierSpec T))
    (links : Finset Link) : FloatingForm S T :=
  { lower := lower
    upper := upper
    links := links
    deletedTier := ∅
    surfaceLinks := links }

/-! ### Predicates on tones and links -/

/-- The tone at index `k` is alive (not deleted). The structural
    primitive; `IsDeleted` is its negation. -/
abbrev IsAlive (f : FloatingForm S T) (k : TierIdx) : Prop := k ∉ f.deletedTier

/-- The tone at index `k` is deleted. Sugar for `¬ IsAlive`. -/
abbrev IsDeleted (f : FloatingForm S T) (k : TierIdx) : Prop := ¬ f.IsAlive k

/-- The tone at index `k` is linked to some TBU on the surface. -/
abbrev IsLinked (f : FloatingForm S T) (k : TierIdx) : Prop :=
  ∃ l ∈ f.surfaceLinks, l.fst = k

/-- The tone at index `k` is floating (alive but unlinked). -/
abbrev IsFloating (f : FloatingForm S T) (k : TierIdx) : Prop :=
  f.IsAlive k ∧ ¬ f.IsLinked k

/-- A surface link `(k, i)` is **tautomorphic** iff its tone and TBU
    share a morpheme. Out-of-range indices on either side make this
    false. Used by *TAUTDOCK and the tautomorphic vs heteromorphic
    distinction discussed in the module docstring. -/
abbrev IsTautomorphic (f : FloatingForm S T) (l : Link) : Prop :=
  (f.upper[l.fst]?).map TierSpec.morpheme =
    (f.lower[l.snd]?).map SegSpec.morpheme ∧
  (f.upper[l.fst]?).isSome

/-! ### Atomic GEN operations -/

/-- (6c) Delete the underlying tone at index `k`. Cascades to remove
    any surface link referencing it. -/
def deleteTierElem (f : FloatingForm S T) (k : TierIdx) : FloatingForm S T :=
  { f with
    deletedTier := insert k f.deletedTier
    surfaceLinks := f.surfaceLinks.filter (λ l => l.fst ≠ k) }

/-- (6a) Insert a surface link `(k, i)`. -/
def insertLink (f : FloatingForm S T) (k : TierIdx) (i : SegIdx) : FloatingForm S T :=
  { f with surfaceLinks := insert (k, i) f.surfaceLinks }

/-- (6b) Delete the surface link `(k, i)`. -/
def deleteLink (f : FloatingForm S T) (k : TierIdx) (i : SegIdx) : FloatingForm S T :=
  { f with surfaceLinks := f.surfaceLinks.erase (k, i) }

/-! ### Well-formedness: no crossing lines -/

/-- A candidate link `(k, i)` would **cross** an existing surface link.
    Wraps the substrate `IndexCrosses` defined over `Finset (ℕ × ℕ)`;
    `IsNoCrossing` (via mathlib's `MonovaryOn`) provides the set-level
    NCC and inherits mathlib's lemma library. -/
abbrev Crosses (f : FloatingForm S T) (k : TierIdx) (i : SegIdx) : Prop :=
  IndexCrosses f.surfaceLinks k i

/-! ### GEN: one-step candidate generation -/

/-- One-step GEN. Enumerates: (a) the faithful candidate, (b) deleting
    each alive tone, (c) for each FLOATING tone, inserting a link to
    each TBU that doesn't cross an existing link. Subset of paper
    eq. 6: omits (d) insert-and-associate and (e) shift, which fig. 3
    doesn't use. The no-crossing filter ([goldsmith-1976])
    enforces autosegmental well-formedness — without it, a floating H
    could dock across an intervening linked tone, which the paper's
    GEN implicitly forbids. -/
def gen (f : FloatingForm S T) : Finset (FloatingForm S T) :=
  let aliveIdxs := (Finset.range f.upper.length).filter (λ k => f.IsAlive k)
  let floatIdxs := aliveIdxs.filter (λ k => ¬ f.IsLinked k)
  let segIdxs := Finset.range f.lower.length
  let deleteOps := aliveIdxs.image (λ k => f.deleteTierElem k)
  let insertOps := ((floatIdxs ×ˢ segIdxs).filter
    (λ ⟨k, i⟩ => ¬ f.Crosses k i)).image (λ ⟨k, i⟩ => f.insertLink k i)
  insert f (deleteOps ∪ insertOps)

/-! ### Indicator vectors for constraint evaluation -/

/-- Indicator vector for floating-tone presence at each underlying-tone
    position, in tier order. Entry `k` is `1` iff `ulTones[k]` is
    currently floating, else `0`. Used by directional `*FLOAT`
    (paper, eq. 16). -/
def floatIndicator (f : FloatingForm S T) : List Nat :=
  (List.range f.upper.length).map λ k => if f.IsFloating k then 1 else 0

/-- Surface tones linked to TBU `i`, returned in tier order (smallest
    tone index first). Used by *FALL and *CROWD. We iterate over
    `List.range f.upper.length` so the result is naturally sorted
    and reduces well via kernel `decide` (avoiding `Finset.sort`,
    which doesn't unfold structurally). -/
def linksTo (f : FloatingForm S T) (i : SegIdx) : List TierIdx :=
  (List.range f.upper.length).filter λ k => (k, i) ∈ f.surfaceLinks

/-- Sequence of tier values linked to backbone position `i`, in tier
    order. -/
def tierValues (f : FloatingForm S T) (i : SegIdx) : List T :=
  (f.linksTo i).filterMap λ k => f.upper[k]?.map TierSpec.value

/-! ### Tier and morpheme subsequences -/

/-- Indices of alive (non-deleted) underlying tones, in tier order.
    Iterates `List.range f.upper.length` so the result is naturally
    sorted and reduces well via kernel `decide`. -/
def aliveTierIdxs (f : FloatingForm S T) : List TierIdx :=
  (List.range f.upper.length).filter (λ k => f.IsAlive k)

/-- Segment indices belonging to morpheme `m`, in segmental order.
    Out-of-range indices are excluded by construction. -/
def segsOfMorpheme (f : FloatingForm S T) (m : Morpheme) : List SegIdx :=
  (List.range f.lower.length).filter (λ i =>
    (f.lower[i]?).map SegSpec.morpheme = some m)

end FloatingForm

end Phonology.Autosegmental
