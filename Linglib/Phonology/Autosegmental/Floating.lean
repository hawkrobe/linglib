/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Morphology.MorphWord
import Linglib.Phonology.Autosegmental.AR
import Linglib.Phonology.Autosegmental.NonCrossing
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

## Main results

* `FloatingForm.gen_preserves_isPlanar` — GEN is closed on the no-crossing WFC
  ([goldsmith-1976] / [pulleyblank-1986]): every one-step candidate of a planar
  surface graph is itself planar.

## Implementation notes

A `FloatingForm` carries an immutable **underlying** state (the inherited
`Graph`: `lower`, `upper`, `links`) and a mutable **surface** state
(`deletedTier`, `surfaceLinks`); GEN modifies only the surface. A tier element
is **floating** iff it is alive (not deleted) and no surface link references it.
This multi-element-per-position encoding (vs. the prior `tonalOverwrite`) is what
[mcpherson-lamont-2026]'s `*CROWD` / `*FALL` constraints require.

`gen` is a paper-subset (delete tier element, insert/delete link; no
insert-and-associate or shift), filtered for no-crossing ([goldsmith-1976]). A
link is **tautomorphic** when its tier element and backbone share a morpheme
(`*TAUTDOCK`, after [wolf-2007]).
-/

namespace Autosegmental

-- Re-export `Morpheme` so autosegmental consumers see it unqualified
-- after `open Autosegmental`.
export Morphology.WordStructure (Morpheme)

/-! ### Tier and link primitives -/

/-- Index into the upper tier. -/
abbrev TierIdx := ℕ

/-- Index into the lower tier. -/
abbrev SegIdx := ℕ

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
    f!"⟨lower={repr (f.lower.toList.map SegSpec.seg)}, upper={repr f.upper.toList}⟩"

namespace FloatingForm

variable {S T : Type*} [DecidableEq S] [DecidableEq T] (f : FloatingForm S T)

/-! ### Surface graph (derived view) -/

/-- The **surface graph**: same tiers as the underlying graph but with
    `surfaceLinks` in place of `links`. Makes the underlying/surface
    duality explicit — both states are `Graph`s sharing tier data. -/
@[reducible] def surfaceGraph : Graph (TierSpec T) (SegSpec S) :=
  { f.toGraph with links := f.surfaceLinks }

/-! ### Construction -/

/-- Construct an input form: surface state mirrors underlying state,
    nothing deleted, all underlying links intact. -/
def mkInput (lower : List (SegSpec S)) (upper : List (TierSpec T))
    (links : Finset Link) : FloatingForm S T :=
  { lower := .ofList lower
    upper := .ofList upper
    links := links
    deletedTier := ∅
    surfaceLinks := links }

/-! ### Morphemic structure -/

/-- The morpheme of the `k`-th upper-tier element, or `none` if out of range. -/
def upperMorpheme? (k : TierIdx) : Option Morpheme := (f.upper.get? (k)).map TierSpec.morpheme

/-- The morpheme of the `i`-th lower-tier element, or `none` if out of range. -/
def lowerMorpheme? (i : SegIdx) : Option Morpheme := (f.lower.get? (i)).map SegSpec.morpheme

/-- Every morpheme occurring on either tier. -/
def morphemes : Finset Morpheme :=
  (f.lower.toList.map SegSpec.morpheme).toFinset ∪ (f.upper.toList.map TierSpec.morpheme).toFinset

/-! ### Predicates on tier elements and links -/

/-- The upper-tier element at index `k` is alive (not deleted). The structural
    primitive; `IsDeleted` is its negation. -/
abbrev IsAlive (k : TierIdx) : Prop := k ∉ f.deletedTier

/-- The upper-tier element at index `k` is deleted. Sugar for `¬ IsAlive`. -/
abbrev IsDeleted (k : TierIdx) : Prop := ¬ f.IsAlive k

/-- The upper-tier element at index `k` is linked to a backbone position
    on the surface. -/
abbrev IsLinked (k : TierIdx) : Prop := ∃ l ∈ f.surfaceLinks, l.fst = k

/-- The upper-tier element at index `k` is floating: in-bounds, alive (not
    deleted), and unlinked. The in-bounds guard mirrors the substrate's
    `Graph.IsFloatingUpper`, so out-of-range indices are not spuriously
    floating. -/
abbrev IsFloating (k : TierIdx) : Prop := k < f.upper.len ∧ f.IsAlive k ∧ ¬ f.IsLinked k

/-- A surface link `(k, i)` is **tautomorphic** iff its upper- and lower-tier
    endpoints share a morpheme. Out-of-range indices on either side make this
    false. -/
abbrev IsTautomorphic (l : Link) : Prop :=
  f.upperMorpheme? l.fst = f.lowerMorpheme? l.snd ∧ (f.upper.get? (l.fst)).isSome

/-! ### Faithfulness: surface vs underlying -/

/-- A surface link absent underlyingly — inserted by GEN (`DEP` / `*TAUTDOCK` source). -/
abbrev IsInsertedLink (l : Link) : Prop := l ∈ f.surfaceLinks ∧ l ∉ f.links

/-- An underlying link absent on the surface — deleted by GEN (`MAX` source). -/
abbrev IsDeletedLink (l : Link) : Prop := l ∈ f.links ∧ l ∉ f.surfaceLinks

/-! ### Atomic GEN operations -/

/-- Delete the underlying upper-tier element at index `k`. Cascades to remove
    any surface link referencing it. -/
def deleteTierElem (k : TierIdx) : FloatingForm S T :=
  { f with
    deletedTier := insert k f.deletedTier
    surfaceLinks := f.surfaceLinks.filter (λ l => l.fst ≠ k) }

/-- Insert a surface link `(k, i)`. -/
def insertLink (k : TierIdx) (i : SegIdx) : FloatingForm S T :=
  { f with surfaceLinks := insert (k, i) f.surfaceLinks }

/-- Delete the surface link `(k, i)`. -/
def deleteLink (k : TierIdx) (i : SegIdx) : FloatingForm S T :=
  { f with surfaceLinks := f.surfaceLinks.erase (k, i) }

/-! ### Well-formedness: no crossing lines -/

/-- A candidate link `(k, i)` would **cross** an existing surface link.
    Wraps the substrate `IndexCrosses` on the candidate link `(k, i)`;
    `IsNonCrossing` (via mathlib's `MonovaryOn`) provides the set-level
    NCC and inherits mathlib's lemma library. -/
abbrev Crosses (k : TierIdx) (i : SegIdx) : Prop :=
  IndexCrosses f.surfaceLinks (k, i)

/-! ### GEN: one-step candidate generation -/

/-- One-step GEN: the faithful candidate, deleting each alive tone, and (for
    each FLOATING tone) inserting a link to each TBU that doesn't cross an
    existing link. A subset of [mcpherson-lamont-2026]'s GEN — omits
    insert-and-associate and shift. The no-crossing filter ([goldsmith-1976])
    enforces well-formedness: without it a floating tone could dock across an
    intervening linked tone. -/
def gen : Finset (FloatingForm S T) :=
  let aliveIdxs := (Finset.range f.upper.len).filter (λ k => f.IsAlive k)
  let floatIdxs := aliveIdxs.filter (λ k => ¬ f.IsLinked k)
  let segIdxs := Finset.range f.lower.len
  let deleteOps := aliveIdxs.image (λ k => f.deleteTierElem k)
  let insertOps := ((floatIdxs ×ˢ segIdxs).filter
    (λ ⟨k, i⟩ => ¬ f.Crosses k i)).image (λ ⟨k, i⟩ => f.insertLink k i)
  insert f (deleteOps ∪ insertOps)

/-- **GEN preserves the no-crossing WFC** ([goldsmith-1976] / [pulleyblank-1986]).
    If the surface graph is planar, every one-step GEN candidate is too: deletes
    shrink the surface link set (`IsNonCrossing.subset`), and each inserted link
    passed the `¬ Crosses` filter (`IsNonCrossing.insert_of_not_indexCrosses`).
    So `gen` is closed on the structural well-formedness condition. -/
theorem gen_preserves_isPlanar (h : f.surfaceGraph.IsPlanar) :
    ∀ g ∈ f.gen, g.surfaceGraph.IsPlanar := by
  have h' : IsNonCrossing f.surfaceLinks := h
  intro g hg
  show IsNonCrossing g.surfaceLinks
  simp only [gen, Finset.mem_insert, Finset.mem_union, Finset.mem_image, Finset.mem_filter,
    Finset.mem_product] at hg
  rcases hg with rfl | ⟨k, _, rfl⟩ | ⟨⟨k, i⟩, ⟨_, hnx⟩, rfl⟩
  · exact h'
  · exact IsNonCrossing.subset (Finset.filter_subset _ _) h'
  · exact IsNonCrossing.insert_of_not_indexCrosses h' hnx

/-! ### Indicator vectors for constraint evaluation -/

/-- Indicator vector of floating upper-tier elements, in tier order: entry `k`
    is `1` iff `upper[k]` is currently floating, else `0`. Drives directional
    floating constraints (e.g. `*FLOAT`). -/
def floatIndicator : List ℕ :=
  (List.range f.upper.len).map λ k => if f.IsFloating k then 1 else 0

/-- Upper-tier elements surface-linked to backbone position `i`, in tier order
    (smallest index first). `List.range`-based so the result is naturally sorted
    and reduces under kernel `decide` (avoiding `Finset.sort`, which doesn't
    unfold structurally). -/
def linksTo (i : SegIdx) : List TierIdx :=
  (List.range f.upper.len).filter λ k => (k, i) ∈ f.surfaceLinks

/-- Sequence of tier values linked to backbone position `i`, in tier
    order. -/
def tierValues (i : SegIdx) : List T :=
  (f.linksTo i).filterMap λ k => (f.upper.get? k).map TierSpec.value

/-! ### Tier and morpheme subsequences -/

/-- Indices of alive (non-deleted) underlying upper-tier elements, in tier
    order; `List.range`-based so it reduces under kernel `decide`. -/
def aliveTierIdxs : List TierIdx :=
  (List.range f.upper.len).filter (λ k => f.IsAlive k)

/-- Lower-tier (backbone) indices belonging to morpheme `m`, in order.
    Out-of-range indices are excluded by construction. -/
def segsOfMorpheme (m : Morpheme) : List SegIdx :=
  (List.range f.lower.len).filter (λ i => f.lowerMorpheme? i = some m)

/-! ### Position counts -/

/-- Count upper-tier positions satisfying decidable `p`. `List.range`-based so it
    reduces under kernel `decide` (avoiding `Finset` pipelines). -/
def countUpper (p : TierIdx → Prop) [DecidablePred p] : ℕ :=
  (List.range f.upper.len).countP (λ k => decide (p k))

/-- Count lower-tier (backbone) positions satisfying decidable `p`. -/
def countLower (p : SegIdx → Prop) [DecidablePred p] : ℕ :=
  (List.range f.lower.len).countP (λ i => decide (p i))

end FloatingForm

end Autosegmental
