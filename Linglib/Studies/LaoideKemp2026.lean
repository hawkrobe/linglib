/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.Floating
import Linglib.Phonology.Autosegmental.Junction
import Linglib.Phonology.Autosegmental.AR
import Linglib.Phonology.Autosegmental.Embedding

/-!
# Laoide-Kemp (2026): Irish preverbal *d'* as a floating segment
[laoide-kemp-2026]

[laoide-kemp-2026] resolves an apparent ordering paradox in Irish
initial consonant mutation (ICM). The preverbal tense particle *d'*
(glossed `HIST`) is usually taken as the *trigger* of lenition on the
following verb, yet its appearance is *conditioned on* the post-lenition
form: *d'* surfaces before vowel-initial verbs (`d' ól` 'I drank')
and before lenited *f*-initial verbs (`d' fhág` 'I left'), but not
before C-initial verbs (`*d' bhog`).

If *d'* is the trigger of lenition, how can its insertion depend on the
output of lenition? The autosegmental answer (Figs. 1, 2, 5 of the
paper): the historic-tense morpheme is `(d) + {L}` where **both
elements are floating**. `{L}` (the lenition-inducing bundle) docks
onto the immediately-following consonant if present; `(d)` is a
floating melodic segment that surfaces only if it can link to an
adjacent C-skeleton position that is both *segmentally empty* and
*directly followed by a non-empty V-slot*. C-initial verbs leave the
first C-slot full; vowel-initial verbs leave it empty; *f*-initial
verbs leave it empty after `{L}` deletes the *f* segmental content.

The analysis is **strictly modular** in the sense of
[bermudez-otero-2012]: morphosyntax inserts the floating
morpheme in *all* phonological contexts, and the phonology determines
whether `(d)` surfaces by ordinary representational constraints. The
paper contrasts this with a morphosyntactic alternative (two separate
`[+HIST]` exponents in different spell-out cycles) and argues
empirically against it on the basis of Munster Irish (§6.1) and
past-tense impersonal mutation resistance (§6.2).

## Grounding: `FloatingForm` over a CV backbone

This file is founded on `Autosegmental.FloatingForm CVKind
Segment` — the project's floating-autosegmental substrate, which
[laoide-kemp-2026]'s floating consonants are a named motivating
consumer of. Three substrate features carry the analysis directly:

* **Morpheme membership** on every tier/backbone element distinguishes
  the historic-tense `(d)`, the verb stem, and the past-tense
  impersonal exponent.
* The **underlying/surface split** (`links` vs `surfaceLinks`) models
  lenition the way the paper does — as a *delinking* of the *f*
  segment from its skeletal slot, leaving the underlying form intact
  and the C-slot surface-empty (`FloatingForm.deleteTierElem`).
* The historic-tense and impersonal exponents are **prefixed by
  `Graph.concat`**, so the morpheme composition the paper draws (Fig. 1:
  `(d)` to the left of the stem; Fig. 5: an empty CV unit to the left)
  is true by construction, not stipulated.

Lenition is keyed on the melodic element linked to the **leftmost
skeletal slot** (`initialConsonantIdx`), not the leftmost melody
element: in a prefixed form (Fig. 5) the stem's *f* is no longer
adjacent to the left edge, and the empty CV unit correctly blocks
`{L}` from docking onto it.

## What this file formalises

* §1 An Irish segment type and CV-skeleton kind.
* §2 Morphemes (`HIST`, the stem, `PST.IMPERS`).
* §3 Verb-stem `FloatingForm`s for `bog`, `ól`, `fág`.
* §4 The exponents `(d)`/`{L}` and the empty-CV impersonal prefix,
  composed onto stems via `Graph.concat`.
* §5 Lenition modelled as surface delinking of *f* on the leftmost
  consonant (the `{L}` effect).
* §6 The docking predicate `dPrimeSurfaces` — Laoide-Kemp's central
  empirical generalisation, formulated on the surface graph.
* §7 Worked-example theorems for Figs. 1a (`bog → bhog`), 1b
  (`ól → d' ól`), 1c (`fág → d' fhág`), and 5 (past-tense impersonals
  `bogadh`, `óladh`, `fágadh`, all `*d'`).

## What this file does NOT formalise

* **Figure 2 (r-initial vs fr-initial)** — `rith` (r-initial; *d'*
  cannot dock because the first C-slot has /r/) and `freagair`
  (fr-initial; `{L}` deletes /f/, leaving an empty C in an
  Infrasegmental Government domain that licenses `(d)`-docking
  despite the empty V-slot pattern). The IG-domain account requires
  [scheer-1998] substrate which linglib doesn't carry yet; deferred.
* **§6.1 Munster Irish dialectal variation** — `dh'` appears after
  *all* lenition-triggering preverbal particles in Munster, not just
  historic tense. The paper argues this is naturally accommodated by
  positing `(d)` as part of the lenition bundle in Munster; encoded
  here as a docstring sketch only.
* **§5 morphosyntactic alternative** — the rejected analysis using
  two separate `[+HIST]` exponents in different spell-out cycles.
  Encoded only via the *predictions* the phonological account makes
  (§6 of this file); the alternative would predict the same
  distribution for Standard Irish but fails the Munster and
  impersonal tests (paper §6).

## Convention

`(d)` and `{L}` in the paper are typeset with parentheses and braces
to indicate floating status. In Lean identifiers we write `dPrime`
and the `HIST` morpheme. `{L}` itself is modelled as the lenition
*process* (`lenite`) rather than a distinct tier element, matching the
paper's treatment of it as abstract lenition-inducing material; `(d)`
is modelled as a genuine floating melodic segment (`Segment.dPrime`).
-/

namespace LaoideKemp2026

open Autosegmental

/-! ## §1 Segment inventory and CV skeleton

A minimal Irish segment inventory sufficient for the paper's
worked examples. Only the segments appearing in `bog`, `ól`, `fág`,
and their past-tense impersonals are enumerated; full Irish phonology
lives in `Fragments/Irish/` (currently absent — Celtic phonology is a
flagged gap in linglib).
-/

/-- Irish segment, minimal coverage. -/
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

/-- Is the segment `f` (the target of the special lenition →
    deletion rule in the paper's §2.2)? -/
def Segment.isF : Segment → Bool
  | .f => true
  | _  => false

/-- CV-skeleton kind. A 2-kind skeleton (`C` for consonant slot, `V`
    for vowel slot), matching the Strict-CV convention
    ([lowenstamm-1996]); a project-canonical Strict-CV substrate
    does not exist (see CLAUDE.md for the deferral rationale). -/
inductive CVKind
  | C
  | V
  deriving DecidableEq, Repr

/-! ## §2 Morphemes

Every tier and backbone element of a `FloatingForm` carries morpheme
membership. We tag the three morphemes the analysis distinguishes:
the verb stem (a free word), the historic-tense exponent `HIST`
(carrying floating `(d)`), and the past-tense impersonal exponent
(carrying the empty CV unit; §6.2).
-/

/-- The verb-stem morpheme (a free word), keyed by orthographic form. -/
private def mStem (s : String) : Morpheme := { form := s, gloss := "" }

/-- The historic-tense exponent, bearing floating `(d)` and `{L}`. -/
private def mHist : Morpheme := { form := "d'", gloss := "HIST" }

/-- The past-tense impersonal exponent: an empty CV unit at the left
    edge ([laoide-kemp-2026] §6.2, Fig. 5). -/
private def mImpers : Morpheme := { form := "", gloss := "PST.IMPERS" }

/-! ## §3 Verb stems as `FloatingForm`s

A verb stem is a `FloatingForm CVKind Segment`: the **upper** tier is
the segmental melody (`Segment`), the **lower** tier is the CV
skeleton (`CVKind`), and association lines `(k, j)` link melody
element `k` to skeleton position `j`. The surface state mirrors the
underlying state on input (`FloatingForm.mkInput`).
-/

/-- A melodic tier element bearing morpheme `m`. -/
private def mel (s : Segment) (m : Morpheme) : TierSpec Segment := ⟨s, m⟩

/-- A skeletal backbone slot bearing morpheme `m`. -/
private def slot (c : CVKind) (m : Morpheme) : SegSpec CVKind := ⟨c, m⟩

/-- Build a single-morpheme verb stem from its CV skeleton, melody,
    and association lines. -/
private def stemForm (name : String) (skeleton : List CVKind)
    (melody : List Segment) (links : Finset (Nat × Nat)) :
    FloatingForm CVKind Segment :=
  let m := mStem name
  FloatingForm.mkInput (skeleton.map (slot · m)) (melody.map (mel · m)) links

/-- The verb `bog` 'soft', the C-initial example in [laoide-kemp-2026]
    Fig. 1a. Melody = [b, o, g]; skeleton = [C, V, C]; identity
    associations. -/
def bog : FloatingForm CVKind Segment :=
  stemForm "bog" [.C, .V, .C] [.b, .o, .g] {(0, 0), (1, 1), (2, 2)}

/-- The verb `ól` 'drink', the V-initial example in
    [laoide-kemp-2026] Fig. 1b. Melody = [ó, l]; skeleton =
    [C, V, C, V]; the initial C-slot has no melodic association.
    This is the key structural property: the underlying form has an
    empty C-slot at position 0. -/
def ól : FloatingForm CVKind Segment :=
  stemForm "ol" [.C, .V, .C, .V] [.ó, .l] {(0, 1), (1, 2)}

/-- The verb `fág` 'leave', the *f*-initial example in
    [laoide-kemp-2026] Fig. 1c. Melody = [f, á, g]; skeleton =
    [C, V, C]; identity associations. Under lenition, the `f`
    segmental content deletes, leaving an empty C₁-slot — exactly
    the configuration that licenses `(d)`-docking. -/
def fág : FloatingForm CVKind Segment :=
  stemForm "fag" [.C, .V, .C] [.f, .á, .g] {(0, 0), (1, 1), (2, 2)}

/-! ## §4 The exponents and morpheme composition

The historic-tense morpheme contributes a **floating** `(d)` melodic
segment with no skeleton of its own (it docks onto the stem's
skeleton). The past-tense impersonal morpheme contributes an **empty
CV unit** — a `[C, V]` skeleton with no melody (Fig. 5). Both are
prefixed onto a stem with `Graph.concat`, which shifts the stem's
association lines by the prefix's tier lengths.
-/

/-- The historic-tense exponent: a floating `(d)` melodic segment,
    no skeleton, no associations ([laoide-kemp-2026] Fig. 1). -/
def historicExponent : FloatingForm CVKind Segment where
  upper := .ofList [mel .dPrime mHist]
  lower := .empty
  links := ∅
  deletedTier := ∅
  surfaceLinks := ∅

/-- The past-tense impersonal exponent: an empty CV unit (`[C, V]`
    skeleton), no melody, no associations ([laoide-kemp-2026] §6.2,
    Fig. 5). -/
def impersonalExponent : FloatingForm CVKind Segment where
  upper := .empty
  lower := .ofList [slot .C mImpers, slot .V mImpers]
  links := ∅
  deletedTier := ∅
  surfaceLinks := ∅

/-- Prefix the historic-tense exponent onto a stem (Fig. 1): floating
    `(d)` becomes melody index 0; the stem's melody shifts right by one. -/
def withHist (stem : FloatingForm CVKind Segment) : FloatingForm CVKind Segment :=
  historicExponent.hconcat stem

/-- Prefix the empty-CV impersonal exponent onto a stem (Fig. 5): the
    stem's skeleton shifts right by two, so the left edge is an empty
    `C₀V₀` unit. -/
def withImpers (stem : FloatingForm CVKind Segment) : FloatingForm CVKind Segment :=
  impersonalExponent.hconcat stem

/-! ## §5 Lenition: the `{L}` deletion rule for *f*

The Irish lenition mutation has many surface effects (stop → fricative,
voiceless → voiced, etc.) but the only effect relevant to the
distribution of `(d)` is the **deletion of word-initial /f/**
([laoide-kemp-2026] §2.2; [gussmann-1986],
[ni-chiosain-1991]). Under the autosegmental analysis,
the lenition-inducing bundle `{L}` docks onto the initial consonant
and deletes its segmental content; the C-skeletal slot remains
behind, surface-empty.

We model this as a **surface delinking** (`deleteTierElem`): the *f*
melody element is deleted from the surface, leaving its C-slot
surface-empty while the underlying form is preserved. Lenition targets
the consonant linked to the **leftmost skeletal slot** — in a prefixed
impersonal form (Fig. 5), the stem's *f* is no longer at the left edge,
so `{L}` cannot reach it and the *f* stays unmutated.
-/

/-- The melody index of the consonant linked to the leftmost skeletal
    slot (skeleton position 0), if any — the target of `{L}`. -/
def initialConsonantIdx (f : FloatingForm CVKind Segment) : Option Nat :=
  (List.range f.upper.len).find? (fun k => (k, 0) ∈ f.surfaceLinks)

/-- Apply lenition: if the consonant on the leftmost skeletal slot is
    `f`, delete its melodic content on the surface (leaving the slot
    surface-empty). All other surface effects of lenition (b → v, etc.)
    are out of scope for the *d'* distribution question. -/
def lenite (f : FloatingForm CVKind Segment) : FloatingForm CVKind Segment :=
  match initialConsonantIdx f with
  | some k => if (f.upper.get? k).map TierSpec.value = some .f then f.deleteTierElem k else f
  | none   => f

/-! ## §6 The docking predicate

`(d)` surfaces iff the post-lenition surface form has an empty C-slot
at position 0 directly followed by a non-empty V-slot at position 1
([laoide-kemp-2026] §4, Fig. 1). The predicate inspects the
**surface graph** (`FloatingForm.surfaceGraph`): the actual `(d)`
surfacing is then a deterministic consequence of the autosegmental
linking convention.
-/

/-- Skeleton position `j` is a C-slot. -/
def isCSlot (f : FloatingForm CVKind Segment) (j : Nat) : Prop :=
  (f.lower.get? j).map SegSpec.seg = some .C

instance (f : FloatingForm CVKind Segment) (j : Nat) : Decidable (isCSlot f j) :=
  inferInstanceAs (Decidable (_ = _))

/-- Skeleton position `j` is a V-slot. -/
def isVSlot (f : FloatingForm CVKind Segment) (j : Nat) : Prop :=
  (f.lower.get? j).map SegSpec.seg = some .V

instance (f : FloatingForm CVKind Segment) (j : Nat) : Decidable (isVSlot f j) :=
  inferInstanceAs (Decidable (_ = _))

/-- The configuration that licenses `(d)`-docking, evaluated on the
    surface graph: position 0 is an empty C-slot, position 1 is a
    non-empty V-slot. The structural predicate at the heart of the
    paper's analysis ([laoide-kemp-2026] §4.1). -/
def dDockable (f : FloatingForm CVKind Segment) : Prop :=
  isCSlot f 0 ∧ ¬ f.SurfaceLinkedLower 0 ∧
    isVSlot f 1 ∧ f.SurfaceLinkedLower 1

instance (f : FloatingForm CVKind Segment) : Decidable (dDockable f) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- `(d)` surfaces in the historic-tense form `f` iff the post-lenition
    surface form is `(d)`-dockable. [laoide-kemp-2026] §4.1. -/
def dPrimeSurfaces (f : FloatingForm CVKind Segment) : Prop :=
  dDockable (lenite f)

instance (f : FloatingForm CVKind Segment) : Decidable (dPrimeSurfaces f) :=
  inferInstanceAs (Decidable (dDockable _))

/-! ## §7 Worked examples (paper Figs. 1a, 1b, 1c)

The three figures in [laoide-kemp-2026] §4.1 establish the
core empirical pattern. In every historic-tense form, `(d)` is melody
index 0 and is **floating** before docking — the floating status the
whole analysis turns on. -/

/-- `(d)` is floating (alive but unlinked) in the historic-tense form
    of every stem before docking — the premise of the analysis. -/
theorem dPrime_floating_bog : (withHist bog).IsFloating 0 := by decide

/-- **Fig. 1a (C-initial: `bog`).** The first C-slot is occupied by
    `b`; `(d)` cannot dock. Lenition affects `b` (b → v / β) but
    *does not vacate the C-slot* — there is still a segment there.
    `(d)` therefore stays unpronounced: `dDockable` fails on the
    `¬ IsLinkedLower 0` conjunct (C₁ is surface-linked to `b`). -/
theorem bog_no_dPrime : ¬ dPrimeSurfaces (withHist bog) := by decide

/-- **Fig. 1b (V-initial: `ól`).** The underlying form has an empty
    C₁-slot already (the vowel `ó` associates to V₁, not to C₀).
    Lenition is a no-op: C₀ has no linked consonant (the verb is
    V-initial), so `{L}` has nothing to delete. `dDockable` holds;
    `(d)` surfaces. The historic form is `d' ól`. -/
theorem ól_yes_dPrime : dPrimeSurfaces (withHist ól) := by decide

/-- **Fig. 1c (*f*-initial: `fág`).** Underlyingly, `f` occupies C₁
    and `(d)` would not be able to dock. Lenition deletes `f`'s
    segmental content on the surface (via `lenite`), leaving C₁
    surface-empty; `dDockable` then holds on the lenited form;
    `(d)` surfaces. The historic tense form is `d' fhág`. -/
theorem fág_yes_dPrime : dPrimeSurfaces (withHist fág) := by decide

/-! ## §8 Past-tense impersonals (paper Fig. 5)

Past tense impersonal verbs carry an underlying **empty CV unit** at
their left edge ([laoide-kemp-2026] §6.2, Fig. 5), modelled here by
prefixing `impersonalExponent` with `Graph.concat`. This empty unit
does double duty: `{L}` cannot dock onto the stem's initial consonant
(it is no longer adjacent to the left edge — `lenite` is a no-op), and
the empty `C₀` is followed by an **empty** `V₀`, so the `(d)`-docking
condition `IsLinkedLower 1` fails. Both effects fall out of the same
piece of structure, and `(d)` never surfaces — exactly the paper's
account of why preverbal *d'* is absent on past-tense impersonals. -/

/-- **Fig. 5a (C-initial impersonal: `bogadh`).** `*d' bogadh`. -/
theorem bogadh_no_dPrime : ¬ dPrimeSurfaces (withHist (withImpers bog)) := by decide

/-- **Fig. 5b (V-initial impersonal: `óladh`).** `*d' óladh` — the
    empty `V₀` of the impersonal prefix breaks the docking condition
    even though the verb is V-initial. -/
theorem óladh_no_dPrime : ¬ dPrimeSurfaces (withHist (withImpers ól)) := by decide

/-- **Fig. 5c (*f*-initial impersonal: `fágadh`).** `*d' fágadh` — the
    empty `C₀` blocks `{L}` from docking onto the stem's `f` (so `f`
    stays, unlike Fig. 1c), and the empty `V₀` blocks `(d)`. -/
theorem fágadh_no_dPrime : ¬ dPrimeSurfaces (withHist (withImpers fág)) := by decide

/-! ## §9 Side-by-side: the paper's empirical core

Putting the theorems together gives [laoide-kemp-2026]'s central
observation: in Standard Irish historic tense, `(d)` surfaces *iff*
the verb is V-initial (Fig. 1b) or *f*-initial (Fig. 1c), but not
when C-initial (Fig. 1a); and it never surfaces on past-tense
impersonals (Fig. 5), regardless of the stem's initial segment. -/

/-- The paper's central empirical generalisation, Figs. 1 + 5. -/
theorem laoideKemp_fig1_fig5 :
    (¬ dPrimeSurfaces (withHist bog) ∧ dPrimeSurfaces (withHist ól) ∧
      dPrimeSurfaces (withHist fág)) ∧
    (¬ dPrimeSurfaces (withHist (withImpers bog)) ∧
      ¬ dPrimeSurfaces (withHist (withImpers ól)) ∧
      ¬ dPrimeSurfaces (withHist (withImpers fág))) :=
  ⟨⟨bog_no_dPrime, ól_yes_dPrime, fág_yes_dPrime⟩,
   ⟨bogadh_no_dPrime, óladh_no_dPrime, fágadh_no_dPrime⟩⟩

/-! ## §10 Modularity: the analysis lives in the monoidal subcategory

[laoide-kemp-2026]'s strict-modularity thesis, formalised against the
monoidal-subcategory framework (`Autosegmental.WellFormedAR`).
Three theorems, one per modular commitment: the morpheme is *composed*
by the monoidal product `⊗ = concat` (not inserted by a non-local
rule); the composition *preserves well-formedness* because the
No-Crossing Constraint is morpheme-modular (`ncc_isMonoidal`); and
the `(d)`-surfacing decision is *left-edge local* — invariant under
material appended on the right (no look-ahead, the apparent paradox
dissolved). -/

/-- The historic-tense morpheme is composed by the monoidal product:
    `withHist stem` is literally `historicExponent ⊗ stem`. The formal
    content of "morphosyntax *concatenates* the floating morpheme"
    ([bermudez-otero-2012]'s strict modularity) — not a non-local
    insertion rule. -/
theorem withHist_eq_concat (stem : FloatingForm CVKind Segment) :
    withHist stem = historicExponent.hconcat stem := rfl

/-- Composing the historic-tense morpheme preserves autosegmental
    well-formedness — a direct consequence of the No-Crossing
    Constraint being morpheme-modular. The floating `(d)` shifts the
    stem's links monotonically, never creating a crossing line. -/
theorem withHist_isPlanar (stem : FloatingForm CVKind Segment)
    (hP : IsNonCrossing stem.links) : IsNonCrossing (withHist stem).links := by
  rw [withHist_eq_concat, FloatingForm.hconcat_links]
  simp only [historicExponent, Finset.empty_union]
  exact hP.image_monotone (ρ := (· + 1)) fun _ _ h => Nat.add_le_add_right h 1

/-- A concrete suffix used to probe right-insensitivity. -/
private def someSuffix : FloatingForm CVKind Segment :=
  stemForm "ma" [.C, .V] [.m, .a] {(0, 0), (1, 1)}

/-- **Left-edge locality (no look-ahead), concrete witness.** Appending
    phonological material on the right of the stem does not change whether
    `(d)` surfaces. Shown here for `ól` with a concrete suffix; the general
    statement (any suffix, configuration level) is
    `dDockable_withHist_concat_right` below. This is the categorical
    resolution of the paper's apparent ordering paradox — the conditioning
    *looks* boundary-spanning but is in fact morpheme-local. -/
theorem dPrime_right_invariant :
    dPrimeSurfaces (withHist ól) ↔
      dPrimeSurfaces (withHist ((ól.hconcat someSuffix))) := by
  decide

/-! ### The general no-look-ahead theorem

`dPrime_right_invariant` above is the concrete witness; here it is for
*every* suffix. The floating `(d)` shifts melody indices only, so
surface-linkedness of a skeletal slot reduces to the stem's underlying
links; and suffix material concatenated on the right lands at skeletal
positions `≥ stem.lower.len`, never touching slots `0`/`1`. The
docking configuration is therefore determined by the stem's left edge
alone — the formal content of strict modularity (no look-ahead). -/

/-- Surface-linkedness of skeletal slot `j` on a historic-tense form
    reduces to the stem having an underlying link to `j`: the floating
    `(d)` shifts melody indices only, never skeletal ones. -/
private theorem isLinkedLower_withHist (X : FloatingForm CVKind Segment) (j : Nat) :
    (withHist X).SurfaceLinkedLower j ↔ ∃ a, (a, j) ∈ X.links := by
  have hlinks : (withHist X).surfaceLinks = X.links.image (shiftLink 1 0) := by
    rw [withHist_eq_concat, FloatingForm.hconcat_surfaceLinks]
    simp [historicExponent]
  constructor
  · rintro ⟨p, hp, hpj⟩
    rw [hlinks, Finset.mem_image] at hp
    obtain ⟨q, hq, hqp⟩ := hp
    refine ⟨q.1, ?_⟩
    have hqj : q.2 = j := by
      have h2 := congrArg Prod.snd hqp
      simp only [shiftLink_apply, Nat.add_zero] at h2
      rw [h2]; exact hpj
    rw [← hqj]; exact hq
  · rintro ⟨a, ha⟩
    refine ⟨(a + 1, j), ?_, rfl⟩
    rw [hlinks, Finset.mem_image]
    exact ⟨(a, j), ha, by simp [shiftLink]⟩

/-- A link to a low skeletal slot (`j < stem.lower.len`) is unaffected
    by appending a suffix: the suffix's links are shifted to slots
    `≥ stem.lower.len`, never reaching `j`. -/
private theorem linked_concat_low (stem suffix : FloatingForm CVKind Segment) {j : Nat}
    (hj : j < stem.lower.len) :
    (∃ a, (a, j) ∈ (stem.hconcat suffix).links) ↔
      ∃ a, (a, j) ∈ stem.links := by
  rw [FloatingForm.hconcat_links]
  constructor
  · rintro ⟨a, ha⟩
    rw [Finset.mem_union] at ha
    rcases ha with h | h
    · exact ⟨a, h⟩
    · exfalso
      rw [Finset.mem_image] at h
      obtain ⟨q, _, hqe⟩ := h
      have hsnd := congrArg Prod.snd hqe
      simp only [shiftLink_apply] at hsnd
      omega
  · rintro ⟨a, ha⟩
    exact ⟨a, Finset.mem_union.2 (Or.inl ha)⟩

/-- The skeletal (lower) tier of a historic form is the stem's — the
    floating `(d)` contributes no skeletal slot. -/
private theorem withHist_lower (Y : FloatingForm CVKind Segment) :
    (withHist Y).lower = Y.lower := by
  rw [withHist_eq_concat, FloatingForm.hconcat_lower]
  exact LabeledTuple.empty_concat Y.lower

/-- The melodic (upper) tier of a historic form is `(d)` concatenated with the
    stem's — used to compute upper-tier lengths in the locality proofs. -/
private theorem withHist_upper (Y : FloatingForm CVKind Segment) :
    (withHist Y).upper = historicExponent.upper.concat Y.upper := by
  rw [withHist_eq_concat, FloatingForm.hconcat_upper]

/-- **The general no-look-ahead theorem.** For *any* suffix, the
    `(d)`-docking configuration of the historic-tense form is determined
    by the stem's left two skeletal slots alone — appending phonological
    material on the right cannot change it (the stem already supplies
    those slots). The general form of `dPrime_right_invariant`: the
    formal content of strict modularity. (The post-*lenition* version
    `dPrimeSurfaces` additionally requires `{L}`-docking to be left-local,
    which holds for in-bounds stems; this is the configuration-level
    statement, on which it rests.) -/
theorem dDockable_withHist_concat_right (stem suffix : FloatingForm CVKind Segment)
    (h2 : 2 ≤ stem.lower.len) :
    dDockable (withHist ((stem.hconcat suffix))) ↔
      dDockable (withHist stem) := by
  have hlow : ∀ j, j < stem.lower.len →
      (withHist ((stem.hconcat suffix))).lower.get? j =
        (withHist stem).lower.get? j := by
    intro j hj
    rw [withHist_lower, withHist_lower, FloatingForm.hconcat_lower,
      LabeledTuple.get?_concat_left hj]
  have hlink : ∀ j, j < stem.lower.len →
      ((withHist ((stem.hconcat suffix))).SurfaceLinkedLower j ↔
        (withHist stem).SurfaceLinkedLower j) := by
    intro j hj
    rw [isLinkedLower_withHist, isLinkedLower_withHist]
    exact linked_concat_low stem suffix hj
  unfold dDockable isCSlot isVSlot
  rw [hlow 0 (by omega), hlow 1 (by omega), hlink 0 (by omega), hlink 1 (by omega)]

/-! ### Lifting to the post-lenition predicate

The configuration-level theorem above is pre-lenition. The full
`dPrimeSurfaces` version additionally needs `{L}`-docking (`lenite`) to
be left-local: `lenite` targets the consonant on skeletal slot 0, which
is the stem's, and deletes the same melody index in both forms. This
needs the stem **in-bounds** (`stem.InBounds`): otherwise a stem
link with an out-of-range melody index would sit outside `withHist
stem`'s `initialConsonantIdx` search range but inside the longer suffixed
range, and `lenite` could target different indices. -/

/-- A surface link to a low skeletal slot (`j < stem.lower.len`) is
    present in the suffixed form iff present in the stem's — the
    pointwise (per `(k, j)`) version of `linked_concat_low`, used both
    for `initialConsonantIdx` and after `deleteTierElem`. -/
private theorem mem_surfaceLinks_concat (stem suffix : FloatingForm CVKind Segment)
    {k j : Nat} (hj : j < stem.lower.len) :
    (k, j) ∈ (withHist ((stem.hconcat suffix))).surfaceLinks ↔
      (k, j) ∈ (withHist stem).surfaceLinks := by
  have hsB : (withHist ((stem.hconcat suffix))).surfaceLinks =
      (stem.hconcat suffix).links.image (shiftLink 1 0) := by
    rw [withHist_eq_concat, FloatingForm.hconcat_surfaceLinks]
    simp [historicExponent]
  have hsA : (withHist stem).surfaceLinks =
      stem.links.image (shiftLink 1 0) := by
    rw [withHist_eq_concat, FloatingForm.hconcat_surfaceLinks]
    simp [historicExponent]
  rw [hsB, hsA, FloatingForm.hconcat_links, Finset.image_union, Finset.mem_union]
  have hfalse : (k, j) ∉ (suffix.links.image
      (shiftLink stem.upper.len stem.lower.len)).image (shiftLink 1 0) := by
    rw [Finset.image_image, Finset.mem_image]
    rintro ⟨⟨a, b⟩, _, he⟩
    have hsnd := congrArg Prod.snd he
    simp only [Function.comp_apply, shiftLink_apply] at hsnd
    omega
  tauto

/-- `List.find?` over `range n` is unchanged by extending `n`, provided
    the predicate is `false` on the new tail — the search never reaches it. -/
private theorem find?_range_stable {p : Nat → Bool} {m n : Nat} (hmn : m ≤ n)
    (htail : ∀ i, m ≤ i → p i = false) :
    (List.range n).find? p = (List.range m).find? p := by
  cases hm : (List.range m).find? p with
  | none =>
    rw [List.find?_range_eq_none] at hm ⊢
    intro i _
    by_cases h : i < m
    · exact hm i h
    · simp [htail i (by omega)]
  | some k =>
    rw [List.find?_range_eq_some] at hm ⊢
    obtain ⟨hpk, hk, hmin⟩ := hm
    rw [List.mem_range] at hk
    exact ⟨hpk, List.mem_range.mpr (by omega), hmin⟩

/-- **`{L}`-docking is left-local.** `lenite` targets the same melody
    index in the historic form of the stem and of the suffixed stem:
    the slot-0 search predicate agrees (`mem_surfaceLinks_concat`) and,
    by `InBounds`, the stem's slot-0 links sit inside its own melody
    range, so the longer suffixed search finds no extra match. -/
private theorem initialConsonantIdx_concat (stem suffix : FloatingForm CVKind Segment)
    (h2 : 2 ≤ stem.lower.len) (hib : stem.InBounds) :
    initialConsonantIdx (withHist ((stem.hconcat suffix)))
      = initialConsonantIdx (withHist stem) := by
  have hpt : (fun k => decide ((k, 0) ∈
        (withHist ((stem.hconcat suffix))).surfaceLinks)) =
      (fun k => decide ((k, 0) ∈ (withHist stem).surfaceLinks)) :=
    funext fun k => decide_eq_decide.mpr (mem_surfaceLinks_concat stem suffix (by omega))
  have eA : (withHist stem).upper.len = stem.upper.len + 1 := by
    rw [withHist_upper]; simp [historicExponent, Nat.add_comm]
  unfold initialConsonantIdx
  rw [hpt]
  apply find?_range_stable
  · show (withHist stem).upper.len ≤
      (withHist ((stem.hconcat suffix))).upper.len
    have eB : (withHist ((stem.hconcat suffix))).upper.len =
        stem.upper.len + suffix.upper.len + 1 := by
      rw [withHist_upper, FloatingForm.hconcat_upper]
      simp [historicExponent, LabeledTuple.concat_len]; omega
    omega
  · intro i hi
    simp only [decide_eq_false_iff_not]
    intro hmem
    have hsA : (withHist stem).surfaceLinks = stem.links.image (shiftLink 1 0) := by
      rw [withHist_eq_concat, FloatingForm.hconcat_surfaceLinks]
      simp [historicExponent]
    rw [hsA, Finset.mem_image] at hmem
    obtain ⟨⟨a, b⟩, hab, he⟩ := hmem
    have hfst := congrArg Prod.fst he
    simp only [shiftLink_apply] at hfst
    have hin1 : a < stem.upper.len := (hib (a, b) hab).1
    rw [eA] at hi
    omega

/-- The docking configuration is right-local even after `lenite` deletes
    melody index `k`: `deleteTierElem k` only filters `surfaceLinks` and
    leaves the lower tier, so the slot-0/1 agreement survives. -/
private theorem dDockable_deleteTierElem_concat (stem suffix : FloatingForm CVKind Segment)
    (h2 : 2 ≤ stem.lower.len) (k : Nat) :
    dDockable ((withHist ((stem.hconcat suffix))).deleteTierElem k) ↔
      dDockable ((withHist stem).deleteTierElem k) := by
  have hlow : ∀ j, j < stem.lower.len →
      ((withHist ((stem.hconcat suffix))).deleteTierElem k).lower.get? j =
        ((withHist stem).deleteTierElem k).lower.get? j := by
    intro j hj
    show (withHist ((stem.hconcat suffix))).lower.get? j =
      (withHist stem).lower.get? j
    rw [withHist_lower, withHist_lower, FloatingForm.hconcat_lower,
      LabeledTuple.get?_concat_left hj]
  have hlink : ∀ j, j < stem.lower.len →
      (((withHist ((stem.hconcat suffix))).deleteTierElem k).SurfaceLinkedLower j ↔
        ((withHist stem).deleteTierElem k).SurfaceLinkedLower j) := by
    intro j hj
    show (∃ p ∈ (withHist ((stem.hconcat suffix))).surfaceLinks.filter
        (fun l => l.fst ≠ k), p.snd = j) ↔
      (∃ p ∈ (withHist stem).surfaceLinks.filter (fun l => l.fst ≠ k), p.snd = j)
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨p, ⟨hmem, hne⟩, hsnd⟩
      have hp : p = (p.1, j) := Prod.ext rfl hsnd
      rw [hp] at hmem
      exact ⟨p, ⟨hp ▸ (mem_surfaceLinks_concat stem suffix hj).mp hmem, hne⟩, hsnd⟩
    · rintro ⟨p, ⟨hmem, hne⟩, hsnd⟩
      have hp : p = (p.1, j) := Prod.ext rfl hsnd
      rw [hp] at hmem
      exact ⟨p, ⟨hp ▸ (mem_surfaceLinks_concat stem suffix hj).mpr hmem, hne⟩, hsnd⟩
  unfold dDockable isCSlot isVSlot
  rw [hlow 0 (by omega), hlow 1 (by omega), hlink 0 (by omega), hlink 1 (by omega)]

/-- **The general no-look-ahead theorem, post-lenition.** For any suffix,
    whether `(d)` *surfaces* — `dPrimeSurfaces`, i.e. dockability after
    `{L}`-lenition — is determined by the stem's left edge alone. Both
    the docking configuration (`dDockable_withHist_concat_right`) and the
    `{L}`-docking target (`initialConsonantIdx_concat`, needing
    `InBounds`) are left-local, so the full predicate is too. This is
    the paper's central claim, in full: preverbal *d'* never looks
    rightward past the word it attaches to. -/
theorem dPrimeSurfaces_withHist_concat_right (stem suffix : FloatingForm CVKind Segment)
    (h2 : 2 ≤ stem.lower.len) (hib : stem.InBounds) :
    dPrimeSurfaces (withHist ((stem.hconcat suffix))) ↔
      dPrimeSurfaces (withHist stem) := by
  have hk : ∀ k, initialConsonantIdx (withHist stem) = some k →
      (withHist ((stem.hconcat suffix))).upper.get? k =
        (withHist stem).upper.get? k := by
    intro k hoi
    have hk_lt : k < (withHist stem).upper.len :=
      List.mem_range.mp (List.mem_of_find?_eq_some hoi)
    have hsplit : (withHist ((stem.hconcat suffix))).upper =
        (withHist stem).upper.concat suffix.upper := by
      rw [withHist_upper, FloatingForm.hconcat_upper, withHist_upper,
        LabeledTuple.concat_assoc]
    rw [hsplit, LabeledTuple.get?_concat_left hk_lt]
  unfold dPrimeSurfaces lenite
  rw [initialConsonantIdx_concat stem suffix h2 hib]
  cases hoi : initialConsonantIdx (withHist stem) with
  | none =>
    dsimp only
    exact dDockable_withHist_concat_right stem suffix h2
  | some k =>
    dsimp only
    rw [hk k hoi]
    split
    · exact dDockable_deleteTierElem_concat stem suffix h2 k
    · exact dDockable_withHist_concat_right stem suffix h2

/-! ## §11 Layer 2 — the historic morpheme as a monoidal-category functor

The deepest categorical content: morpheme *prefixation* is not merely a
function on representations but an **endofunctor on the monoidal
category** `WellFormedAR` — mathlib's `tensorLeft`. This consumes the full
`MonoidalCategory (WellFormedAR α β)` instance (not merely the `concat`
operation), and the **associativity of prefixation** is `WellFormedAR`'s
associator, exhibited by `tensorLeftTensor` — a natural isomorphism
that does not exist without coherence (pentagon + triangle).

`(d)` acts on the left edge, so it is *left*-tensoring (`tensorLeft`),
not right: the categorical encoding of the morpheme's **directionality**
as a preverbal particle rather than a suffix.

The remaining Layer-2 frontier — modelling *lenition* and *docking*
themselves as functors `WellFormedAR ⥤ WellFormedAR` (acting on morphisms, not just
objects) — is left open. The conjecture is that they are functorial
only over the precedence-preserving `Graph.SubgraphEmbeds`, not over
all of `AR.Hom`; settling it either way is a genuine result. The
extensional content (no look-ahead) is fully captured by
`dPrimeSurfaces_withHist_concat_right` above: for any suffix, whether
`(d)` surfaces depends only on the stem's left edge. -/

/-- The historic-tense exponent as an object of the monoidal category of
    representations: one floating `(d)` melody node, no skeleton, no links. -/
def historicExponentRep :
    Representation (Sigma.fst :
      ((b : Bool) × TwoTier (TierSpec Segment) (SegSpec CVKind) b) → Bool) :=
  Representation.ofData
    (fun b => match b with
      | true => ([mel .dPrime mHist] : List (TwoTier (TierSpec Segment) (SegSpec CVKind) true))
      | false => [])
    ⊥

open CategoryTheory MonoidalCategory in
/-- **The historic morpheme is an endofunctor on `WellFormedAR`.** Prefixing `(d)`
    is left-tensoring by `historicExponentAR` — mathlib's `tensorLeft`,
    which exists only because `WellFormedAR` is a `MonoidalCategory`. Left- rather
    than right-tensoring encodes the morpheme's directionality as a
    preverbal particle. -/
def withHistFunctor :
    Representation (Sigma.fst :
        ((b : Bool) × TwoTier (TierSpec Segment) (SegSpec CVKind) b) → Bool) ⥤
    Representation (Sigma.fst :
        ((b : Bool) × TwoTier (TierSpec Segment) (SegSpec CVKind) b) → Bool) :=
  tensorLeft historicExponentRep

open CategoryTheory MonoidalCategory in
/-- The functor's action on objects *is* morpheme prefixing: the tensor of
    the exponent with the stem. -/
theorem withHistFunctor_obj
    (X : Representation (Sigma.fst :
        ((b : Bool) × TwoTier (TierSpec Segment) (SegSpec CVKind) b) → Bool)) :
    withHistFunctor.obj X = historicExponentRep ⊗ X := rfl

open CategoryTheory MonoidalCategory in
/-- **Associativity of prefixation is the associator.** This natural
    isomorphism — prefixing the compound `(d) ⊗ X` equals prefixing `X`
    then prefixing `(d)` — is built from `WellFormedAR`'s associator, so it does
    not exist unless the monoidal structure is *coherent* (pentagon +
    triangle). It is the concrete artifact that makes `WellFormedAR`'s coherence
    load-bearing rather than decorative. -/
noncomputable def prefixAssoc
    (X : Representation (Sigma.fst :
        ((b : Bool) × TwoTier (TierSpec Segment) (SegSpec CVKind) b) → Bool)) :
    tensorLeft (historicExponentRep ⊗ X) ≅
      tensorLeft X ⋙ tensorLeft historicExponentRep :=
  tensorLeftTensor historicExponentRep X

/-! ## §11.5 The morphism-functor frontier: why lenition is precedence-sensitive

Layer 2 modelled morpheme *prefixing* as the functor `tensorLeft`. The
deeper question is whether a phonological *process* — `{L}`-lenition — is
a functor on the autosegmental category, acting on morphisms and not just
objects. At the graph level, lenition is `delinkInitial`: erase the
association lines to the leftmost (word-initial) skeletal slot.

The answer is a sharp dichotomy. `delinkInitial` is **not** a functor on
the full category `AR α β`: a label-preserving reindexing
(`AR.Hom`) can move a non-initial element into initial position, after
which there is *no* morphism between the delinked images at all
(`delinkInitial_not_functorial`). But over `PrecAR`, the
**precedence-preserving wide subcategory** (`Autosegmental/Embedding.lean`:
order-embedding tier maps; `SubgraphEmbeds` translations are canonical
instances), it lifts to a genuine endofunctor `delinkInitialFunctor`
(built from `delinkInitial_map` / `_id` / `_comp`; precedence-preservation
discharges the reflects-initial-slot hypothesis via
`precPreserving.reflects_zero`). This is the categorical content of the
linguistic fact that lenition targets the *word-initial* consonant: the
process is functorial over exactly the maps that preserve precedence. -/

section Frontier

open Autosegmental

/-- Lenition's structural model on the foundation: erase the association
    lines at the word-initial (tier-initial) skeletal position —
    `MixedGraphCat.delinkMin`. Its functoriality over precedence-preserving
    morphisms is the substrate theorem `Autosegmental.delinkMinFunctor`;
    here we exhibit the **negative half**: on the broad category the lift
    fails, because a label-preserving reindexing can move a non-initial
    slot into initial position. -/
private abbrev negA :
    Representation (Sigma.fst : ((b : Bool) × TwoTier Unit Bool b) → Bool) :=
  Representation.ofData
    (fun b => match b with
      | true => ([()] : List (TwoTier Unit Bool true))
      | false => [false, true])
    (fun i j p q => i = true ∧ j = false ∧ p = 0 ∧ q = 1)

private abbrev negB :
    Representation (Sigma.fst : ((b : Bool) × TwoTier Unit Bool b) → Bool) :=
  Representation.ofData
    (fun b => match b with
      | true => ([()] : List (TwoTier Unit Bool true))
      | false => [true, false])
    (fun i j p q => i = true ∧ j = false ∧ p = 0 ∧ q = 0)

/-- The label-preserving swap of the two skeletal slots: a broad morphism
    (it does not preserve precedence). -/
private def negSwap : MixedGraphCat.Hom negA.obj negB.obj where
  toFun v := match v with
    | ⟨true, p⟩ => ⟨true, p⟩
    | ⟨false, ⟨0, _⟩⟩ => ⟨false, ⟨1, by decide⟩⟩
    | ⟨false, ⟨1, _⟩⟩ => ⟨false, ⟨0, by decide⟩⟩
  edge_map := by
    rintro ⟨bv, p⟩ ⟨bw, q⟩ ⟨hne, hor⟩
    rcases hor with ⟨rfl, rfl, hp, hq⟩ | ⟨rfl, rfl, hp, hq⟩
    · obtain rfl : p = ⟨0, by decide⟩ := Fin.ext hp
      obtain rfl : q = ⟨1, by decide⟩ := Fin.ext hq
      exact ⟨by decide, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩
    · obtain rfl : q = ⟨0, by decide⟩ := Fin.ext hp
      obtain rfl : p = ⟨1, by decide⟩ := Fin.ext hq
      exact ⟨by decide, Or.inr ⟨rfl, rfl, rfl, rfl⟩⟩
  label_comp := by
    rintro ⟨bv, p⟩
    cases bv
    · match p with
      | ⟨0, _⟩ => rfl
      | ⟨1, _⟩ => rfl
    · rfl

/-- **Delinking is not functorial on the broad category**: `negSwap` is a
    morphism, yet the delinked images admit no morphism at all — the
    surviving slot-1 link of `negA` lands on `negB`'s initial slot, which
    delinking erased. The obstruction is precisely failure to preserve
    precedence (`Autosegmental.delinkMinFunctor` lifts it otherwise). -/
theorem delinkInitial_not_functorial :
    IsEmpty (MixedGraphCat.Hom
      (MixedGraphCat.delinkMin Sigma.fst false negA.obj)
      (MixedGraphCat.delinkMin Sigma.fst false negB.obj)) := by
  refine ⟨fun g => ?_⟩
  let v1 : negA.obj.V := ⟨true, ⟨0, by decide⟩⟩
  let w1 : negA.obj.V := ⟨false, ⟨1, by decide⟩⟩
  have hsurv : (MixedGraphCat.delinkMin Sigma.fst false negA.obj).graph.edges.Adj v1 w1 := by
    refine ⟨⟨by decide, Or.inl ⟨rfl, rfl, rfl, rfl⟩⟩, ?_, ?_⟩
    · rintro ⟨h, -⟩
      exact absurd h (by decide)
    · rintro ⟨-, hmin⟩
      exact hmin ⟨false, ⟨0, by decide⟩⟩ ⟨rfl, by decide⟩
  have htw : (g.toFun w1).1 = false := congrArg Sigma.fst (g.label_comp w1)
  obtain ⟨⟨-, hor⟩, hv, hw⟩ := g.edge_map hsurv
  rcases hor with ⟨-, -, -, hq⟩ | ⟨ht, -, -, -⟩
  · -- the image link lands on negB's initial slot: contradiction with delinking
    refine hw ⟨htw, fun u hu => ?_⟩
    have h2 : (u.2 : ℕ) < ((g.toFun w1).2 : ℕ) := hu.2
    omega
  · -- the symmetric orientation contradicts label preservation
    exact absurd (htw.symm.trans ht) (by decide)

end Frontier

/-! ## §12 The strict-modularity payoff

The phonological analysis above is *strictly modular* in the sense
of [bermudez-otero-2012]: morphosyntax inserts the historic-
tense morpheme `(d) + {L}` uniformly, and the phonology decides
whether `(d)` surfaces by inspecting the post-lenition skeletal
configuration of the verb. No look-ahead in morphology; no
post-lenition reference in spell-out; no module-transcending
diacritic. The paper's §1 frames this in opposition to four
non-modular alternatives:

* **Morphology directly manipulates phonological structure**
  ([anderson-1992]).
* **Readjustment rules triggered by module-transcending
  diacritics** ([harley-noyer-1999]).
* **Co-phonologies** ([anttila-2002], [inkelas-zoll-2007]).
* **Morpheme-specific phonological constraints**
  ([pater-2000], [pater-2009]).

The autosegmental approach with floating phonologically-defective
material ([lieber-1983], [zimmermann-2022]) is the
fifth and only strictly-modular alternative, and it is the one
[laoide-kemp-2026] adopts.

This file does not formalise the other four alternatives directly.
Their predictions for Standard Irish coincide with the
autosegmental account; the discriminating data are in §6 of the
paper (Munster Irish, past-tense impersonals) and are noted in the
module docstring as deferred extensions.
-/

end LaoideKemp2026
