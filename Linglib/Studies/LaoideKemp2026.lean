/-
Copyright (c) 2026 Robert Hawkins. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Hawkins
-/
import Linglib.Phonology.Autosegmental.Graph

/-!
# Laoide-Kemp (2026): Irish preverbal *d'* as a floating segment
@cite{laoide-kemp-2026}

@cite{laoide-kemp-2026} resolves an apparent ordering paradox in Irish
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
@cite{bermudez-otero-2012}: morphosyntax inserts the floating
morpheme in *all* phonological contexts, and the phonology determines
whether `(d)` surfaces by ordinary representational constraints. The
paper contrasts this with a morphosyntactic alternative (two separate
`[+HIST]` exponents in different spell-out cycles) and argues
empirically against it on the basis of Munster Irish (§6.1) and
past-tense impersonal mutation resistance (§6.2).

## What this file formalises

* §1 An Irish segment type covering the paper's examples.
* §2 Verb-stem `Graph`s for `bog`, `ól`, `fág`, encoded as melodic
  tier (segments) over a CV skeleton (`Phonology.Autosegmental.Graph`).
* §3 Lenition modelled as the paper's `{L}` → segment-content
  removal on the leftmost consonant; the `lenite` function.
* §4 The docking predicate `dPrimeSurfaces` — Laoide-Kemp's central
  empirical generalisation, formulated structurally on `Graph`.
* §5 Worked-example theorems for Figs. 1a (`bog → bhog`), 1b
  (`ól → d' ól`), and 1c (`fág → d' fhág`).

## What this file does NOT formalise

* **Figure 2 (r-initial vs fr-initial)** — `rith` (r-initial; *d'*
  cannot dock because the first C-slot has /r/) and `freagair`
  (fr-initial; `{L}` deletes /f/, leaving an empty C in an
  Infrasegmental Government domain that licenses `(d)`-docking
  despite the empty V-slot pattern). The IG-domain account requires
  Scheer 1998 substrate which linglib doesn't carry yet; deferred.
* **Figure 5 (past-tense impersonals)** — `bogadh` carries an
  underlying empty CV unit at the left edge, blocking both
  `{L}`-docking and `(d)`-linking. Needs the prefix-CV substrate;
  sketched in docstring but not encoded as theorems here.
* **§6.1 Munster Irish dialectal variation** — `dh'` appears after
  *all* lenition-triggering preverbal particles in Munster, not just
  historic tense. The paper argues this is naturally accommodated by
  positing `(d)` as part of the lenition bundle in Munster; encoded
  here as a docstring sketch only.
* **§5 morphosyntactic alternative** — the rejected analysis using
  two separate `[+HIST]` exponents in different spell-out cycles.
  Encoded only via the *predictions* the phonological account makes
  (§4 of this file); the alternative would predict the same
  distribution for Standard Irish but fails the Munster and
  impersonal tests (paper §6).

## Convention

`(d)` and `{L}` in the paper are typeset with parentheses and braces
to indicate floating status. In Lean identifiers we write `dPrime`
and `lenitionMark`. The historic-tense morpheme is not constructed as
a separate `Graph` value in this draft; it is captured indirectly via
the `dPrimeSurfaces` predicate on a post-lenition verb stem. A future
extension can model the morpheme as a leftward-concatenated `Graph`
with a floating `(d)` and an explicit `{L}` element on the melodic
tier (Fig. 1 of the paper draws it this way).
-/

namespace LaoideKemp2026

open Phonology.Autosegmental

/-! ## §1 Segment inventory

A minimal Irish segment inventory sufficient for the paper's
worked examples. Only the segments appearing in `bog`, `ól`, `fág`,
`rith`, `freagair`, and `bogadh` are enumerated; full Irish phonology
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

/-! ## §2 CV-skeleton and verb stems

A 2-kind skeleton (`C` for consonant slot, `V` for vowel slot).
This is a *local* definition matching the Strict-CV convention
(@cite{lowenstamm-1996}); a project-canonical Strict-CV substrate
does not exist (see CLAUDE.md for the deferral rationale). Verb
stems are encoded as `Graph Segment CVKind` values: the upper tier
is the segmental melody, the lower tier is the CV skeleton, and the
association lines `(k, j)` link melody element `k` to skeleton
position `j`.
-/

/-- CV-skeleton kind. -/
inductive CVKind
  | C
  | V
  deriving DecidableEq, Repr

/-- A verb-stem skeleton + melody, encoded as an
    `Phonology.Autosegmental.Graph` over Irish segments and CV-kinds.
    Convention: melody is on the **upper** tier, skeleton on the
    **lower** tier, links are `(melody-index, skeleton-index)`. -/
abbrev VerbStem := Graph Segment CVKind

/-- The verb `bog` 'soft', the C-initial example in @cite{laoide-kemp-2026}
    Fig. 1a. Melody = [b, o, g]; skeleton = [C, V, C]; identity
    associations. -/
def bog : VerbStem where
  upper := [.b, .o, .g]
  lower := [.C, .V, .C]
  links := {(0, 0), (1, 1), (2, 2)}

/-- The verb `ól` 'drink', the V-initial example in
    @cite{laoide-kemp-2026} Fig. 1b. Melody = [ó, l]; skeleton =
    [C, V, C, V]; the initial C-slot has no melodic association.
    This is the key structural property: the underlying form has an
    empty C-slot at position 0. -/
def ól : VerbStem where
  upper := [.ó, .l]
  lower := [.C, .V, .C, .V]
  links := {(0, 1), (1, 2)}

/-- The verb `fág` 'leave', the *f*-initial example in
    @cite{laoide-kemp-2026} Fig. 1c. Melody = [f, á, g]; skeleton =
    [C, V, C]; identity associations. Under lenition, the `f`
    segmental content deletes, leaving an empty C₁-slot — exactly
    the configuration that licenses `(d)`-docking. -/
def fág : VerbStem where
  upper := [.f, .á, .g]
  lower := [.C, .V, .C]
  links := {(0, 0), (1, 1), (2, 2)}

/-! ## §3 Lenition: the `{L}` deletion rule for *f*

The Irish lenition mutation has many surface effects (stop → fricative,
voiceless → voiced, etc.) but the only effect relevant to the
distribution of `(d)` is the **deletion of word-initial /f/**
(@cite{laoide-kemp-2026} §2.2; @cite{gussmann-1986},
@cite{ni-chiosain-1991}). Under the autosegmental analysis,
the lenition-inducing bundle `{L}` docks onto the initial consonant
and deletes its segmental content; the C-skeletal slot remains
behind, empty.

We model this minimal slice: `lenite` removes the melodic content at
position 0 if it is /f/, and erases the corresponding association
line. The C-slot itself is preserved (this is the key structural
property — the slot remains, allowing `(d)` to dock).
-/

/-- The leftmost upper-tier element of a verb stem, if any. -/
def VerbStem.firstMelody (v : VerbStem) : Option Segment := v.upper.head?

/-- Apply lenition: if the leftmost melodic segment is `f`, delete
    its association to slot 0 (leaving slot 0 empty). All other
    surface effects of lenition (b→v, etc.) are out of scope for the
    *d'* distribution question. -/
def lenite (v : VerbStem) : VerbStem :=
  match v.firstMelody with
  | some .f => v.eraseLink 0 0
  | _       => v

/-! ## §4 The docking predicate

`(d)` surfaces iff the post-lenition form has an empty C-slot at
position 0 directly followed by a non-empty V-slot at position 1
(@cite{laoide-kemp-2026} §4, Fig. 1). The predicate ignores the
floating `(d)` element itself: it asks whether the *target
configuration* for `(d)`-docking exists in the post-lenition verb
stem. The actual `(d)` surfacing is then a deterministic consequence
of the autosegmental linking convention.
-/

/-- Skeleton position `j` is a C-slot in `v`'s lower tier. -/
def VerbStem.isCSlot (v : VerbStem) (j : Nat) : Prop :=
  v.lower[j]? = some .C

instance (v : VerbStem) (j : Nat) : Decidable (v.isCSlot j) :=
  inferInstanceAs (Decidable (v.lower[j]? = some .C))

/-- Skeleton position `j` is a V-slot in `v`'s lower tier. -/
def VerbStem.isVSlot (v : VerbStem) (j : Nat) : Prop :=
  v.lower[j]? = some .V

instance (v : VerbStem) (j : Nat) : Decidable (v.isVSlot j) :=
  inferInstanceAs (Decidable (v.lower[j]? = some .V))

/-- The configuration that licenses `(d)`-docking: position 0 is an
    empty C-slot, position 1 is a non-empty V-slot. The structural
    predicate at the heart of the paper's analysis. -/
def VerbStem.dDockable (v : VerbStem) : Prop :=
  v.isCSlot 0 ∧ ¬ v.IsLinkedLower 0 ∧ v.isVSlot 1 ∧ v.IsLinkedLower 1

instance (v : VerbStem) : Decidable v.dDockable :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _))

/-- `(d)` surfaces in the historic tense form of `v` iff the
    post-lenition form is `(d)`-dockable.
    @cite{laoide-kemp-2026} §4.1. -/
def dPrimeSurfaces (v : VerbStem) : Prop :=
  (lenite v).dDockable

instance (v : VerbStem) : Decidable (dPrimeSurfaces v) :=
  inferInstanceAs (Decidable (lenite v).dDockable)

/-! ## §5 Worked examples (paper Figs. 1a, 1b, 1c)

The three figures in @cite{laoide-kemp-2026} §4.1 establish the
core empirical pattern.
-/

/-- **Fig. 1a (C-initial: `bog`).** The first C-slot is occupied by
    `b`; `(d)` cannot dock. Lenition affects `b` (b → v / β) but
    *does not vacate the C-slot* — there is still a segment there.
    `(d)` therefore stays unpronounced.

    Our model represents this as: lenition is a no-op on `bog`
    (since the leftmost melody is not `f`), so the post-lenition
    form retains `b` at slot 0, and `dDockable` fails on the
    `¬ IsLinkedLower 0` conjunct. -/
theorem bog_no_dPrime : ¬ dPrimeSurfaces bog := by decide

/-- **Fig. 1b (V-initial: `ól`).** The underlying form has an empty
    C₁-slot already (the vowel `ó` associates to V₁ at index 1, not
    to C₀ at index 0). Lenition is a no-op on `ól` (leftmost
    melody is `ó`, not `f`); `dDockable` holds; `(d)` surfaces. -/
theorem ól_yes_dPrime : dPrimeSurfaces ól := by decide

/-- **Fig. 1c (*f*-initial: `fág`).** Underlyingly, `f` occupies C₁
    and `(d)` would not be able to dock. Lenition deletes `f`'s
    segmental content (via `lenite`, erasing the (0, 0) link),
    leaving C₁ empty; `dDockable` then holds on the lenited form;
    `(d)` surfaces. The historic tense form is `d' fhág`. -/
theorem fág_yes_dPrime : dPrimeSurfaces fág := by decide

/-! ## §6 Side-by-side: the paper's empirical core

Putting the three theorems together gives @cite{laoide-kemp-2026}'s
central observation in one statement: `(d)` surfaces *iff* the
verb is V-initial (Fig. 1b) or *f*-initial (Fig. 1c), but not when
C-initial (Fig. 1a).
-/

/-- The paper's central empirical generalisation, stated for the
    three Fig. 1 verbs. -/
theorem laoideKemp_fig1 :
    ¬ dPrimeSurfaces bog ∧ dPrimeSurfaces ól ∧ dPrimeSurfaces fág :=
  ⟨bog_no_dPrime, ól_yes_dPrime, fág_yes_dPrime⟩

/-! ## §7 The strict-modularity payoff

The phonological analysis above is *strictly modular* in the sense
of @cite{bermudez-otero-2012}: morphosyntax inserts the historic-
tense morpheme `(d) + {L}` uniformly, and the phonology decides
whether `(d)` surfaces by inspecting the post-lenition skeletal
configuration of the verb. No look-ahead in morphology; no
post-lenition reference in spell-out; no module-transcending
diacritic. The paper's §1 frames this in opposition to four
non-modular alternatives:

* **Morphology directly manipulates phonological structure**
  (@cite{anderson-1992}).
* **Readjustment rules triggered by module-transcending
  diacritics** (@cite{harley-noyer-1999}).
* **Co-phonologies** (@cite{anttila-2002}, @cite{inkelas-zoll-2007}).
* **Morpheme-specific phonological constraints**
  (@cite{pater-2000}, @cite{pater-2009}).

The autosegmental approach with floating phonologically-defective
material (@cite{lieber-1983}, @cite{zimmermann-2022}) is the
fifth and only strictly-modular alternative, and it is the one
@cite{laoide-kemp-2026} adopts.

This file does not formalise the other four alternatives directly.
Their predictions for Standard Irish coincide with the
autosegmental account; the discriminating data are in §6 of the
paper (Munster Irish, past-tense impersonals) and are noted in the
module docstring as deferred extensions.
-/

end LaoideKemp2026
