import Linglib.Core.Morphology.MorphWord
import Linglib.Phonology.Autosegmental.GrammaticalTone
import Linglib.Phonology.Autosegmental.NoCrossing
import Linglib.Phonology.Autosegmental.RegisterTier
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Prod

/-!
# Floating tones — autosegmental forms with multi-tone TBUs

Goldsmith-style autosegmental representation: tones live on a tier above
the segmental backbone, connected by **association lines** (links).
Multiple tones can associate to one TBU (forming contours); a tone with
no associations is **floating**.

## Main definitions

* `Link` — an autosegmental link `(tone-index, TBU-index)`.
* `ToneSpec`, `SegSpec` — tier elements carrying morpheme membership
  via `Morphology.WordStructure.Morpheme` (re-exported into this
  namespace).
* `FloatingForm S` — autosegmental form with underlying/surface split.
* `FloatingForm.IsAlive`, `IsLinked`, `IsFloating`, `IsTautomorphic`,
  `Crosses` — decidable predicates on tones and links.
* `FloatingForm.deleteTone`, `insertLink`, `deleteLink` — atomic GEN
  operations (paper subset).
* `FloatingForm.gen` — one-step GEN as a `Finset` of candidate forms.
* `FloatingForm.floatIndicator`, `linksTo`, `toneSequence` — indicator
  vectors for constraint evaluation.

## Implementation notes

The form carries an immutable **underlying** state (`segs`, `ulTones`,
`ulLinks`) and a mutable **surface** state (`deletedTones`,
`surfaceLinks`). GEN operations modify only the surface state. A tone
is **floating** iff it is not deleted and no surface link references
it.

The refactor over the prior overwrite-semantics encoding
(`GrammaticalTone.tonalOverwrite`) is required by
@cite{mcpherson-lamont-2026}: *CROWD penalises TBUs with too many
associated tones, and *FALL penalises HM/HL/ML contours — both of
which presuppose multi-tone-per-TBU representation.

A surface link `(k, i)` is **tautomorphic** iff
`ulTones[k].morpheme = segs[i].morpheme`. *TAUTDOCK (after
@cite{wolf-2007}) penalises tautomorphic links inserted by GEN.

`gen` implements a paper-subset of operations: delete tone, insert
link, delete link. Insert-and-associate and shift operations are
omitted (not needed for the fig. 3 derivation in the source paper).
The no-crossing filter inside GEN enforces autosegmental
well-formedness (@cite{goldsmith-1976}).

## References

* @cite{goldsmith-1976} — autosegmental phonology, no-crossing constraint
* @cite{wolf-2007} — *TAUTDOCK
* @cite{mcpherson-lamont-2026} — grammatical tone with multi-tone TBUs
-/

namespace Phonology.Autosegmental

open Phonology.Autosegmental.RegisterTier (TRN)

-- Re-export `Morpheme` so autosegmental consumers see it unqualified
-- after `open Phonology.Autosegmental`.
export Morphology.WordStructure (Morpheme)

/-! ### Tier and link primitives -/

/-- Index into `ulTones`. -/
abbrev ToneIdx := Nat

/-- Index into `segs`. -/
abbrev SegIdx := Nat

/-- An autosegmental link: tone `fst` is associated to TBU `snd`. -/
abbrev Link := ToneIdx × SegIdx

/-- A tonal-tier element: tone value plus morpheme membership. -/
structure ToneSpec where
  tone : TRN
  morpheme : Morpheme
  deriving DecidableEq, Repr

/-- A segmental backbone element: segment plus morpheme membership.
    Generic over the segment type `S`. -/
structure SegSpec (S : Type*) where
  seg : S
  morpheme : Morpheme
  deriving DecidableEq, Repr

/-! ### `FloatingForm` -/

/-- An autosegmental tonal form. See module docstring for the
    underlying-vs-surface convention. -/
structure FloatingForm (S : Type*) where
  /-- Segmental backbone (tier order). -/
  segs : List (SegSpec S)
  /-- UNDERLYING tonal tier (tier order; immutable). -/
  ulTones : List ToneSpec
  /-- UNDERLYING association lines (immutable). -/
  ulLinks : Finset Link
  /-- SURFACE deletion set (current state). -/
  deletedTones : Finset ToneIdx
  /-- SURFACE association lines (current state). -/
  surfaceLinks : Finset Link
  deriving DecidableEq

/-- Hides the `Finset` fields (mathlib's `Finset.Repr` is `unsafe`) and
    prints only segments and underlying tones; debug-only. -/
instance {S : Type*} [Repr S] : Repr (FloatingForm S) where
  reprPrec f _ :=
    f!"⟨segs={repr (f.segs.map SegSpec.seg)}, ulTones={repr f.ulTones}⟩"

namespace FloatingForm

variable {S : Type*} [DecidableEq S]

/-! ### Construction -/

/-- Construct an input form: surface state mirrors underlying state,
    nothing deleted, all underlying links intact. -/
def mkInput (segs : List (SegSpec S)) (ulTones : List ToneSpec)
    (ulLinks : Finset Link) : FloatingForm S :=
  { segs := segs
    ulTones := ulTones
    ulLinks := ulLinks
    deletedTones := ∅
    surfaceLinks := ulLinks }

/-! ### Predicates on tones and links -/

/-- The tone at index `k` is alive (not deleted). The structural
    primitive; `IsDeleted` is its negation. -/
abbrev IsAlive (f : FloatingForm S) (k : ToneIdx) : Prop := k ∉ f.deletedTones

/-- The tone at index `k` is deleted. Sugar for `¬ IsAlive`. -/
abbrev IsDeleted (f : FloatingForm S) (k : ToneIdx) : Prop := ¬ f.IsAlive k

/-- The tone at index `k` is linked to some TBU on the surface. -/
abbrev IsLinked (f : FloatingForm S) (k : ToneIdx) : Prop :=
  ∃ l ∈ f.surfaceLinks, l.fst = k

/-- The tone at index `k` is floating (alive but unlinked). -/
abbrev IsFloating (f : FloatingForm S) (k : ToneIdx) : Prop :=
  f.IsAlive k ∧ ¬ f.IsLinked k

/-- A surface link `(k, i)` is **tautomorphic** iff its tone and TBU
    share a morpheme. Out-of-range indices on either side make this
    false. Used by *TAUTDOCK and the tautomorphic vs heteromorphic
    distinction discussed in the module docstring. -/
abbrev IsTautomorphic (f : FloatingForm S) (l : Link) : Prop :=
  (f.ulTones[l.fst]?).map ToneSpec.morpheme =
    (f.segs[l.snd]?).map SegSpec.morpheme ∧
  (f.ulTones[l.fst]?).isSome

/-! ### Atomic GEN operations -/

/-- (6c) Delete the underlying tone at index `k`. Cascades to remove
    any surface link referencing it. -/
def deleteTone (f : FloatingForm S) (k : ToneIdx) : FloatingForm S :=
  { f with
    deletedTones := insert k f.deletedTones
    surfaceLinks := f.surfaceLinks.filter (λ l => l.fst ≠ k) }

/-- (6a) Insert a surface link `(k, i)`. -/
def insertLink (f : FloatingForm S) (k : ToneIdx) (i : SegIdx) : FloatingForm S :=
  { f with surfaceLinks := insert (k, i) f.surfaceLinks }

/-- (6b) Delete the surface link `(k, i)`. -/
def deleteLink (f : FloatingForm S) (k : ToneIdx) (i : SegIdx) : FloatingForm S :=
  { f with surfaceLinks := f.surfaceLinks.erase (k, i) }

/-! ### Well-formedness: no crossing lines -/

/-- A candidate link `(k, i)` would **cross** an existing surface link.
    Wraps the substrate `IndexCrosses` defined over `Finset (ℕ × ℕ)`;
    `IsNoCrossing` (via mathlib's `MonovaryOn`) provides the set-level
    NCC and inherits mathlib's lemma library. -/
abbrev Crosses (f : FloatingForm S) (k : ToneIdx) (i : SegIdx) : Prop :=
  IndexCrosses f.surfaceLinks k i

/-! ### GEN: one-step candidate generation -/

/-- One-step GEN. Enumerates: (a) the faithful candidate, (b) deleting
    each alive tone, (c) for each FLOATING tone, inserting a link to
    each TBU that doesn't cross an existing link. Subset of paper
    eq. 6: omits (d) insert-and-associate and (e) shift, which fig. 3
    doesn't use. The no-crossing filter (@cite{goldsmith-1976})
    enforces autosegmental well-formedness — without it, a floating H
    could dock across an intervening linked tone, which the paper's
    GEN implicitly forbids. -/
def gen (f : FloatingForm S) : Finset (FloatingForm S) :=
  let aliveIdxs := (Finset.range f.ulTones.length).filter (λ k => f.IsAlive k)
  let floatIdxs := aliveIdxs.filter (λ k => ¬ f.IsLinked k)
  let segIdxs := Finset.range f.segs.length
  let deleteOps := aliveIdxs.image (λ k => f.deleteTone k)
  let insertOps := ((floatIdxs ×ˢ segIdxs).filter
    (λ ⟨k, i⟩ => ¬ f.Crosses k i)).image (λ ⟨k, i⟩ => f.insertLink k i)
  insert f (deleteOps ∪ insertOps)

/-! ### Indicator vectors for constraint evaluation -/

/-- Indicator vector for floating-tone presence at each underlying-tone
    position, in tier order. Entry `k` is `1` iff `ulTones[k]` is
    currently floating, else `0`. Used by directional `*FLOAT`
    (paper, eq. 16). -/
def floatIndicator (f : FloatingForm S) : List Nat :=
  (List.range f.ulTones.length).map λ k => if f.IsFloating k then 1 else 0

/-- Surface tones linked to TBU `i`, returned in tier order (smallest
    tone index first). Used by *FALL and *CROWD. We iterate over
    `List.range f.ulTones.length` so the result is naturally sorted
    and reduces well via kernel `decide` (avoiding `Finset.sort`,
    which doesn't unfold structurally). -/
def linksTo (f : FloatingForm S) (i : SegIdx) : List ToneIdx :=
  (List.range f.ulTones.length).filter λ k => (k, i) ∈ f.surfaceLinks

/-- Sequence of tone values linked to TBU `i`, in tier order. -/
def toneSequence (f : FloatingForm S) (i : SegIdx) : List TRN :=
  (f.linksTo i).filterMap λ k => f.ulTones[k]?.map ToneSpec.tone

/-! ### Tier and morpheme subsequences -/

/-- Indices of alive (non-deleted) underlying tones, in tier order.
    Iterates `List.range f.ulTones.length` so the result is naturally
    sorted and reduces well via kernel `decide`. -/
def aliveTones (f : FloatingForm S) : List ToneIdx :=
  (List.range f.ulTones.length).filter (λ k => f.IsAlive k)

/-- Segment indices belonging to morpheme `m`, in segmental order.
    Out-of-range indices are excluded by construction. -/
def segsOfMorpheme (f : FloatingForm S) (m : Morpheme) : List SegIdx :=
  (List.range f.segs.length).filter (λ i =>
    (f.segs[i]?).map SegSpec.morpheme = some m)

end FloatingForm

end Phonology.Autosegmental
