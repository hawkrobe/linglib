/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.Floating
import Linglib.Morphology.Word.Tree

/-!
# Laoide-Kemp (2026): Strict modularity at the morphosyntax-phonology interface

This file formalizes the analysis of [laoide-kemp-2026] of the Irish historic-tense particle
*d'*, which appears before vowel-initial and lenited *f*-initial verbs but not before other
consonants ((11)), an apparent paradox for the autosegmental account of initial consonant
mutation, since the particle taken to trigger lenition seems to be inserted only once lenition
has applied. On the paper's account the exponent of historic tense is a floating segment `(d)`
followed by the lenition-inducing bundle `{L}` ((18)): both are inserted in every environment,
`{L}` docks onto the following consonant, deleting the segmental content of an *f* (§2.2), and
`(d)` is pronounced only if it can link to an adjacent skeletal C-slot that is empty and
directly followed by a filled V-slot (§4.1). Over the library's floating autosegmental forms
on a strict-CV skeleton ([lowenstamm-1996]), the historic exponent is prefixed by
concatenation, lenition is the surface delinking of a word-initial *f*, and the docking
condition is read off the surface form: `(d)` surfaces before *ól* and *fág* but not before
*bog* (Figure 1), and never before a past-tense impersonal, whose empty initial CV unit blocks
both lenition and docking (Figure 5, §6.2), the two effects of one piece of structure
(`laoideKemp_fig1_fig5`, `impersonal_blocks_lenition`). The analysis is strictly modular in the
sense of [bermudez-otero-2012]: the morpheme is inserted uniformly and the phonology decides.

## Implementation notes

The segment inventory covers the paper's examples only. Lenition is modelled as the deletion
of *f* alone, the one effect that bears on the distribution of `(d)`, and targets the melody
linked to the leftmost skeletal slot, so the empty CV unit of an impersonal keeps the stem's
*f* out of reach. The infrasegmental-government domains that license `(d)` before the lenited
clusters of (12) (Figure 2, [scheer-1998]), the Munster reanalysis of `(d)` as part of the
lenition bundle (§6.1, Table 3), and the rejected morphosyntactic alternative of §5 are not
modelled.

## TODO

Model Figure 2, the *r*- against *fr*-initial contrast, once a government substrate exists.

## References

* [laoide-kemp-2026]
* [bermudez-otero-2012], [lowenstamm-1996], [gussmann-1986], [ni-chiosain-1991],
  [scheer-1998]
-/

namespace LaoideKemp2026

open Autosegmental
open Morphology (Morph)

/-! ### Segments and skeleton -/

/-- The segments of the paper's worked examples. -/
inductive Segment
  /-- Consonant `b`. -/
  | b
  /-- Consonant `g`. -/
  | g
  /-- Consonant `l`. -/
  | l
  /-- Consonant `f`. -/
  | f
  /-- Consonant `r`. -/
  | r
  /-- Consonant `m`. -/
  | m
  /-- Vowel `o`. -/
  | o
  /-- Vowel `ó`. -/
  | ó
  /-- Vowel `á`. -/
  | á
  /-- Vowel `i`. -/
  | i
  /-- Schwa-like vowel `a` (Irish `a`). -/
  | a
  /-- The historic-tense floating segment `(d)`. -/
  | dPrime
  deriving DecidableEq, Repr

/-- The segment *f*, whose content lenition deletes (§2.2). -/
def Segment.isF : Segment → Bool
  | .f => true
  | _  => false

/-- A slot of the strict-CV skeleton ([lowenstamm-1996]). -/
inductive CVKind
  | C
  | V
  deriving DecidableEq, Repr

/-! ### Morphemes

Every tier and skeletal element carries its morpheme: the verb stem, the historic-tense
exponent bearing the floating `(d)`, and the past-tense impersonal exponent bearing the empty
CV unit (§6.2). -/

/-- The verb-stem morpheme (a free word), keyed by orthographic form. -/
private def mStem (s : String) : Morph := .root s

/-- The historic-tense exponent, bearing `(d)` and `{L}`. -/
private def mHist : Morph := .pref "d'"

/-- The past-tense impersonal exponent (§6.2). -/
private def mImpers : Morph := .pref ""

/-! ### Verb stems

A stem is a floating form whose upper tier is the melody, whose lower tier is the CV skeleton,
and whose association lines `(k, j)` link melody element `k` to skeletal slot `j`; on input the
surface state is the underlying one. -/

/-- A melodic tier element bearing morpheme `m`. -/
private def mel (s : Segment) (m : Morph) : TierSpec Segment Morph := ⟨s, m⟩

/-- A skeletal backbone slot bearing morpheme `m`. -/
private def slot (c : CVKind) (m : Morph) : SegSpec CVKind Morph := ⟨c, m⟩

/-- Build a single-morpheme verb stem from its CV skeleton, melody,
    and association lines. -/
private def stemForm (name : String) (skeleton : List CVKind)
    (melody : List Segment) (links : Finset (Nat × Nat)) :
    FloatingForm CVKind Segment Morph :=
  let m := mStem name
  FloatingForm.mkInput (skeleton.map (slot · m)) (melody.map (mel · m)) links

/-- *bog* 'move', consonant-initial (Figure 1a). -/
def bog : FloatingForm CVKind Segment Morph :=
  stemForm "bog" [.C, .V, .C] [.b, .o, .g] {(0, 0), (1, 1), (2, 2)}

/-- *ól* 'drink', vowel-initial (Figure 1b): the initial C-slot is empty underlyingly. -/
def ól : FloatingForm CVKind Segment Morph :=
  stemForm "ol" [.C, .V, .C, .V] [.ó, .l] {(0, 1), (1, 2)}

/-- *fág* 'leave', *f*-initial (Figure 1c). -/
def fág : FloatingForm CVKind Segment Morph :=
  stemForm "fag" [.C, .V, .C] [.f, .á, .g] {(0, 0), (1, 1), (2, 2)}

/-! ### The exponents

The historic-tense morpheme contributes a floating `(d)` with no skeleton of its own ((18)),
and the past-tense impersonal morpheme an empty CV unit with no melody (Figure 5); each is
prefixed to a stem by concatenation, which shifts the stem's association lines by the prefix's
tier lengths. -/

/-- The historic-tense exponent ((18)): a floating `(d)`, no skeleton, no associations. -/
def historicExponent : FloatingForm CVKind Segment Morph where
  upper := .ofList [mel .dPrime mHist]
  lower := .empty
  links := ∅
  deletedTier := ∅
  surfaceLinks := ∅

/-- The past-tense impersonal exponent (§6.2, Figure 5): an empty CV unit, no melody. -/
def impersonalExponent : FloatingForm CVKind Segment Morph where
  upper := .empty
  lower := .ofList [slot .C mImpers, slot .V mImpers]
  links := ∅
  deletedTier := ∅
  surfaceLinks := ∅

/-- The historic-tense form of a stem: `(d)` becomes melody element 0. -/
def withHist (stem : FloatingForm CVKind Segment Morph) : FloatingForm CVKind Segment Morph :=
  historicExponent.hconcat stem

/-- The past-tense impersonal of a stem: an empty CV unit at the left edge. -/
def withImpers (stem : FloatingForm CVKind Segment Morph) : FloatingForm CVKind Segment Morph :=
  impersonalExponent.hconcat stem

/-! ### Lenition

Of the effects of lenition only the deletion of a word-initial *f* bears on the distribution of
`(d)` (§2.2, [gussmann-1986], [ni-chiosain-1991]): `{L}` docks onto the initial consonant and
removes its segmental content, leaving the skeletal slot behind. This is a surface delinking of
the *f* from its slot, and it targets the melody linked to the leftmost skeletal slot, so that
behind an empty CV unit (Figure 5) the stem's *f* is out of reach. -/

/-- The melody index of the consonant linked to the leftmost skeletal slot, the target of
`{L}`. -/
def initialConsonantIdx (f : FloatingForm CVKind Segment Morph) : Option Nat :=
  (List.range f.upper.len).find? (λ k => (k, 0) ∈ f.surfaceLinks)

/-- Lenition: if the consonant on the leftmost skeletal slot is *f*, delete its melodic
content on the surface, leaving the slot empty. -/
def lenite (f : FloatingForm CVKind Segment Morph) : FloatingForm CVKind Segment Morph :=
  match initialConsonantIdx f with
  | some k => if (f.upper.get? k).map TierSpec.value = some .f then f.deleteTierElem k else f
  | none   => f

/-! ### Docking

`(d)` is pronounced iff, after lenition, the first skeletal slot is an empty C-slot directly
followed by a filled V-slot (§4.1). -/

/-- Skeleton position `j` is a C-slot. -/
def isCSlot (f : FloatingForm CVKind Segment Morph) (j : Nat) : Prop :=
  (f.lower.get? j).map SegSpec.seg = some .C

instance (f : FloatingForm CVKind Segment Morph) (j : Nat) : Decidable (isCSlot f j) :=
  inferInstanceAs (Decidable (_ = _))

/-- Skeleton position `j` is a V-slot. -/
def isVSlot (f : FloatingForm CVKind Segment Morph) (j : Nat) : Prop :=
  (f.lower.get? j).map SegSpec.seg = some .V

instance (f : FloatingForm CVKind Segment Morph) (j : Nat) : Decidable (isVSlot f j) :=
  inferInstanceAs (Decidable (_ = _))

/-- The configuration that licenses the docking of `(d)`, on the surface form: slot 0 an empty
C-slot, slot 1 a filled V-slot (§4.1). -/
def dDockable (f : FloatingForm CVKind Segment Morph) : Prop :=
  isCSlot f 0 ∧ ¬ f.SurfaceLinkedLower 0 ∧
    isVSlot f 1 ∧ f.SurfaceLinkedLower 1

instance (f : FloatingForm CVKind Segment Morph) : Decidable (dDockable f) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- `(d)` surfaces in a historic-tense form iff the lenited form licenses its docking. -/
def dPrimeSurfaces (f : FloatingForm CVKind Segment Morph) : Prop :=
  dDockable (lenite f)

instance (f : FloatingForm CVKind Segment Morph) : Decidable (dPrimeSurfaces f) :=
  inferInstanceAs (Decidable (dDockable _))

/-! ### Figure 1

In every historic-tense form `(d)` is melody element 0 and floating before docking. -/

/-- `(d)` is floating in a historic-tense form before docking. -/
theorem dPrime_floating_bog : (withHist bog).IsFloating 0 := by decide

/-- Figure 1a, *bog* → *bhog*: the first C-slot is occupied, and lenition leaves a segment
in it, so `(d)` cannot dock ((11c)). -/
theorem bog_no_dPrime : ¬ dPrimeSurfaces (withHist bog) := by decide

/-- Figure 1b, *ól* → *d' ól*: the first C-slot is empty underlyingly, `{L}` has nothing to
dock onto, and `(d)` links ((11a)). -/
theorem ól_yes_dPrime : dPrimeSurfaces (withHist ól) := by decide

/-- Figure 1c, *fág* → *d' fhág*: lenition deletes the *f*, leaving the first C-slot empty
on the surface, and `(d)` links ((11b)). -/
theorem fág_yes_dPrime : dPrimeSurfaces (withHist fág) := by decide

/-! ### Figure 5

A past-tense impersonal carries an empty CV unit at its left edge (§6.2), which does double
duty: `{L}` finds no consonant to dock onto, and the empty C-slot is followed by an empty
V-slot, so `(d)` cannot link either ((27)). -/

/-- Figure 5a, *bogadh*: no `(d)`. -/
theorem bogadh_no_dPrime : ¬ dPrimeSurfaces (withHist (withImpers bog)) := by decide

/-- Figure 5b, *óladh*: the empty V-slot of the prefix blocks docking although the verb is
vowel-initial. -/
theorem óladh_no_dPrime : ¬ dPrimeSurfaces (withHist (withImpers ól)) := by decide

/-- Figure 5c, *fágadh*: the empty C-slot keeps `{L}` from the stem's *f*, and the empty
V-slot blocks `(d)`. -/
theorem fágadh_no_dPrime : ¬ dPrimeSurfaces (withHist (withImpers fág)) := by decide

/-- The empirical core: in the historic tense `(d)` surfaces before a vowel-initial or
*f*-initial verb and not before a consonant-initial one, and never before a past-tense
impersonal (Figures 1 and 5). -/
theorem laoideKemp_fig1_fig5 :
    (¬ dPrimeSurfaces (withHist bog) ∧ dPrimeSurfaces (withHist ól) ∧
      dPrimeSurfaces (withHist fág)) ∧
    (¬ dPrimeSurfaces (withHist (withImpers bog)) ∧
      ¬ dPrimeSurfaces (withHist (withImpers ól)) ∧
      ¬ dPrimeSurfaces (withHist (withImpers fág))) :=
  ⟨⟨bog_no_dPrime, ól_yes_dPrime, fág_yes_dPrime⟩,
   ⟨bogadh_no_dPrime, óladh_no_dPrime, fágadh_no_dPrime⟩⟩

/-- Figure 5 from the other side: the empty CV unit leaves `{L}` no consonant to dock onto, so
an impersonal resists lenition even after a lenition-triggering particle ((26b)). -/
theorem impersonal_blocks_lenition : initialConsonantIdx (withImpers fág) = none := by decide

end LaoideKemp2026
