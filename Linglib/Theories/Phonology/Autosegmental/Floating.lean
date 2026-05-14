import Linglib.Theories.Phonology.Autosegmental.RegisterTier
import Linglib.Theories.Phonology.Autosegmental.GrammaticalTone
import Mathlib.Data.Finset.Insert
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Image

/-!
# Floating Tones — Autosegmental Forms with Multi-Tone TBUs
@cite{goldsmith-1976} @cite{wolf-2007} @cite{mcpherson-lamont-2026}

Goldsmith-style autosegmental representation: tones live on a tier above
the segmental backbone, connected by **association lines** (links).
Multiple tones can associate to one TBU (forming contours); a tone with
no associations is **floating**.

This refactor (over the prior overwrite-semantics encoding) is required
by the @cite{mcpherson-lamont-2026} fig. 3 derivation: *CROWD penalises
TBUs with too many associated tones, and *FALL penalises HM/HL/ML
contours — both of which presuppose multi-tone-per-TBU representation.

## Encoding

The form carries an immutable **underlying** state and a mutable
**surface** state. GEN operations modify only the surface state.

Underlying (immutable):
- `segs : List (SegSpec S)` — segmental backbone with morpheme membership
- `ulTones : List ToneSpec` — tier elements with morpheme membership
- `ulLinks : Finset Link` — input association lines

Surface (mutable):
- `deletedTones : Finset ToneIdx` — set of GEN-deleted tone indices
- `surfaceLinks : Finset Link` — current association lines

A tone is **floating** iff it is not deleted AND no surface link
references it.

## Operations (paper, eq. 6 subset)

- `deleteTone k` — paper (6c): mark tone `k` deleted; cascades to remove
  any surface link referencing it
- `insertLink k i` — paper (6a): add link `(k, i)` to surfaceLinks
- `deleteLink k i` — paper (6b): remove link `(k, i)` from surfaceLinks

The paper's GEN also includes (6d) insert+associate a new tone and (6e)
shift a tone (the latter credited to Gietz et al. 2023 in the paper);
both omitted here as they don't appear in the fig. 3 derivation.

## Tautomorphic vs heteromorphic links

A surface link `(k, i)` is **tautomorphic** iff `ulTones[k].morpheme =
segs[i].morpheme`. The constraint *TAUTDOCK (paper, eq. 15, after
@cite{wolf-2007}) penalises tautomorphic links inserted by GEN (i.e.,
in `surfaceLinks` but not in `ulLinks`).
-/

namespace Phonology.Autosegmental

open Phonology.Autosegmental.RegisterTier (TRN)

-- ============================================================================
-- § 1: Tier and Link Primitives
-- ============================================================================

/-- Index into `ulTones`. -/
abbrev ToneIdx := Nat

/-- Index into `segs`. -/
abbrev SegIdx := Nat

/-- Identifier for a morpheme. Concrete IDs are fragment-specific.
    Opaque (`def`, not `abbrev`) so that arithmetic on Nat doesn't
    silently leak through — only the operations declared below
    (DecidableEq, Repr, OfNat literals) are exposed to consumers. -/
def MorphemeId : Type := Nat

namespace MorphemeId
instance : DecidableEq MorphemeId := inferInstanceAs (DecidableEq Nat)
instance : Repr MorphemeId := inferInstanceAs (Repr Nat)
instance : ToString MorphemeId := inferInstanceAs (ToString Nat)
instance (n : Nat) : OfNat MorphemeId n := inferInstanceAs (OfNat Nat n)
end MorphemeId

/-- An autosegmental link: tone `fst` is associated to TBU `snd`. -/
abbrev Link := ToneIdx × SegIdx

/-- A tonal-tier element: tone value plus morpheme membership. -/
structure ToneSpec where
  tone : TRN
  morpheme : MorphemeId
  deriving DecidableEq, Repr

/-- A segmental backbone element: segment plus morpheme membership.
    Generic over the segment type `S`. -/
structure SegSpec (S : Type) where
  seg : S
  morpheme : MorphemeId
  deriving Repr

instance {S : Type} [DecidableEq S] : DecidableEq (SegSpec S) := λ a b => by
  rcases a with ⟨s1, m1⟩
  rcases b with ⟨s2, m2⟩
  exact decidable_of_iff (s1 = s2 ∧ m1 = m2)
    ⟨λ ⟨rfl, rfl⟩ => rfl, λ h => by cases h; exact ⟨rfl, rfl⟩⟩

-- ============================================================================
-- § 2: FloatingForm
-- ============================================================================

/-- An autosegmental tonal form. See module docstring for the
    underlying-vs-surface convention. -/
structure FloatingForm (S : Type) where
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

/-- Repr drops Finset fields (mathlib's Finset.Repr is unsafe). Shows
    only segs and ulTones for debugging. -/
instance {S : Type} [Repr S] : Repr (FloatingForm S) := ⟨λ f _ =>
  s!"⟨segs={repr (f.segs.map SegSpec.seg)}, ulTones={repr f.ulTones}⟩"⟩

instance {S : Type} [DecidableEq S] : DecidableEq (FloatingForm S) := λ a b => by
  rcases a with ⟨a1, a2, a3, a4, a5⟩
  rcases b with ⟨b1, b2, b3, b4, b5⟩
  exact decidable_of_iff
    (a1 = b1 ∧ a2 = b2 ∧ a3 = b3 ∧ a4 = b4 ∧ a5 = b5)
    ⟨λ ⟨rfl, rfl, rfl, rfl, rfl⟩ => rfl,
     λ h => by cases h; exact ⟨rfl, rfl, rfl, rfl, rfl⟩⟩

namespace FloatingForm

variable {S : Type} [DecidableEq S]

-- ============================================================================
-- § 3: Construction
-- ============================================================================

/-- Construct an input form: surface state mirrors underlying state,
    nothing deleted, all underlying links intact. -/
def mkInput (segs : List (SegSpec S)) (ulTones : List ToneSpec)
    (ulLinks : Finset Link) : FloatingForm S :=
  { segs := segs
    ulTones := ulTones
    ulLinks := ulLinks
    deletedTones := ∅
    surfaceLinks := ulLinks }

-- ============================================================================
-- § 4: Predicates on Tones
-- ============================================================================

/-- The tone at index `k` is alive (not deleted). The structural
    primitive; `IsDeleted` is its negation. -/
def IsAlive (f : FloatingForm S) (k : ToneIdx) : Prop := k ∉ f.deletedTones

instance (f : FloatingForm S) (k : ToneIdx) : Decidable (f.IsAlive k) :=
  inferInstanceAs (Decidable (k ∉ f.deletedTones))

/-- The tone at index `k` is deleted. Sugar for `¬ IsAlive`. -/
abbrev IsDeleted (f : FloatingForm S) (k : ToneIdx) : Prop := ¬ f.IsAlive k

/-- The tone at index `k` is linked to some TBU on the surface. -/
def IsLinked (f : FloatingForm S) (k : ToneIdx) : Prop :=
  ∃ l ∈ f.surfaceLinks, l.fst = k

instance (f : FloatingForm S) (k : ToneIdx) : Decidable (f.IsLinked k) :=
  decidable_of_iff (∃ l ∈ f.surfaceLinks, l.fst = k) Iff.rfl

/-- The tone at index `k` is floating (alive but unlinked). -/
def IsFloating (f : FloatingForm S) (k : ToneIdx) : Prop :=
  f.IsAlive k ∧ ¬ f.IsLinked k

instance (f : FloatingForm S) (k : ToneIdx) : Decidable (f.IsFloating k) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- A surface link `(k, i)` is **tautomorphic** iff its tone and TBU
    share a morpheme. Out-of-range indices on either side make this
    false. Used by *TAUTDOCK (paper, eq. 15) and the tautomorphic vs
    heteromorphic distinction discussed in the module docstring. -/
def IsTautomorphic (f : FloatingForm S) (l : Link) : Prop :=
  (f.ulTones[l.fst]?).map ToneSpec.morpheme =
    (f.segs[l.snd]?).map SegSpec.morpheme ∧
  (f.ulTones[l.fst]?).isSome

instance (f : FloatingForm S) (l : Link) : Decidable (f.IsTautomorphic l) :=
  inferInstanceAs (Decidable (_ ∧ _))

-- ============================================================================
-- § 5: Atomic Operations (paper, eq. 6 subset)
-- ============================================================================

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

-- ============================================================================
-- § 6: Well-Formedness — No Crossing Lines
-- ============================================================================

/-- A candidate link `(k, i)` would **cross** an existing surface link
    `(k', i')` iff tier order disagrees with segmental order:
    `(k < k' ∧ i > i') ∨ (k > k' ∧ i < i')`. Crossing-association
    candidates violate the No-Crossing Constraint of @cite{goldsmith-1976}
    autosegmental phonology and are excluded from GEN. -/
def Crosses (f : FloatingForm S) (k : ToneIdx) (i : SegIdx) : Prop :=
  ∃ l ∈ f.surfaceLinks, (k < l.fst ∧ l.snd < i) ∨ (l.fst < k ∧ i < l.snd)

instance (f : FloatingForm S) (k : ToneIdx) (i : SegIdx) :
    Decidable (Crosses f k i) :=
  decidable_of_iff (∃ l ∈ f.surfaceLinks,
    (k < l.fst ∧ l.snd < i) ∨ (l.fst < k ∧ i < l.snd)) Iff.rfl

-- ============================================================================
-- § 7: GEN — One-Step Candidate Generation
-- ============================================================================

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

-- ============================================================================
-- § 8: Indicator Vectors for Constraint Evaluation
-- ============================================================================

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

-- ============================================================================
-- § 9: Tier and Morpheme Subsequences
-- ============================================================================

/-- Indices of alive (non-deleted) underlying tones, in tier order.
    Iterates `List.range f.ulTones.length` so the result is naturally
    sorted and reduces well via kernel `decide`. -/
def aliveTones (f : FloatingForm S) : List ToneIdx :=
  (List.range f.ulTones.length).filter (λ k => decide (f.IsAlive k))

/-- Segment indices belonging to morpheme `m`, in segmental order.
    Out-of-range indices are excluded by construction. -/
def segsOfMorpheme (f : FloatingForm S) (m : MorphemeId) : List SegIdx :=
  (List.range f.segs.length).filter (λ i =>
    decide ((f.segs[i]?).map SegSpec.morpheme = some m))

end FloatingForm

end Phonology.Autosegmental
