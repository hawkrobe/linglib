import Linglib.Theories.Phonology.Autosegmental.RegisterTier
import Linglib.Theories.Phonology.Autosegmental.GrammaticalTone
import Linglib.Theories.Phonology.Autosegmental.Floating

/-!
# Poko Phonological Fragment — Tonal
@cite{mcpherson-dryer-2021} @cite{mcpherson-2022} @cite{mcpherson-lamont-2026}

Poko (also Poko-Rawo, ISO 639-3: not assigned, Glottocode: poko1259) is
a Skou language spoken in Sandaun Province, Papua New Guinea, near the
border with West Papua. ~100 speakers as of @cite{mcpherson-dryer-2021}.

## Tone system

Three contrastive tone levels — high (H), mid (M), low (L) — plus
toneless syllables and floating tones. Lexical melodies range from `Ø`
(toneless) through `M`, `MH`, `LM`, `LH`, `M^H` (M with floating H);
@cite{mcpherson-2022} argues the lexical inventory excludes simple `L`
and `H` melodies as a response to OCP markedness pressures.

The TBU is the syllable; stems are mono- or disyllabic with vowel-final
stems undergoing apocope phrase-medially (paper, ex. 1).

## Floating tones

Floating L tones appear at the LEFT edge of stems; floating H tones at
the RIGHT edge (paper, §2.2). Postlexically, floating L tones remain
floating (causing downstep), while floating H tones either dock
rightward, dock leftward (tautomorphic, blocked by `*TAUTDOCK`), or
delete (paper, §3.2).

## Stems represented here

Just enough syllables for the @cite{mcpherson-lamont-2026} fig. 3
demonstration: `kāk` (3sg.m possessive), `rī` (pig stem with `/M^H/`
melody), `dō` (get verb with `/M^H/` melody). Promote to a fuller
fragment when a second Poko paper arrives.

## Morpheme IDs

Each Poko stem is one morpheme. We assign Nat morpheme IDs in
left-to-right order of first appearance in the fig. 3 input:
`kāk = 0`, `rī = 1`, `dō = 2`. The IDs are consumed by *TAUTDOCK and
*CROWD via the `SegSpec`/`ToneSpec` morpheme fields.
-/

namespace Fragments.Poko

open Phonology.Autosegmental
open Phonology.Autosegmental.RegisterTier (TRN)

-- ============================================================================
-- § 1: Syllables
-- ============================================================================

/-- Poko syllables represented for the @cite{mcpherson-lamont-2026}
    tableaux: fig. 3 (`kak`, `ri`, `do`); eq. (24) (`nan`, `ri`, `na`);
    eq. (27) (`kak`, `ka`); eq. (30) (`kak`, `ili`). Promote to a
    fuller stem inventory when a second Poko paper arrives. -/
inductive Syll
  | kak  -- 3sg.m possessive `kāk`
  | ri   -- pig stem `rī` (M^H lexical melody)
  | do   -- get verb `dō` (M^H lexical melody)
  | nan  -- 1sg subject pronoun `nãn`
  | na   -- eat verb `nã`
  | ka   -- friend stem `kā` (MH lexical melody, paper eq. 26a)
  | ili  -- bamboo stem `ìlí` (LH lexical melody, paper eq. 28a)
  | ne   -- 'make.1sg' verb stem `ne` (toneless, paper eq. 22a)
  deriving DecidableEq, Repr, Inhabited

-- ============================================================================
-- § 2: Morpheme IDs
-- ============================================================================

/-- Stable morpheme ID per stem. IDs are assigned to keep inputs from
    distinct paper examples non-overlapping. -/
def Syll.morphemeId : Syll → MorphemeId
  | .kak => 0
  | .ri  => 1
  | .do  => 2
  | .nan => 3
  | .na  => 4
  | .ka  => 5
  | .ili => 6
  | .ne  => 7

-- ============================================================================
-- § 3: Convenience Constructors for SegSpec / ToneSpec
-- ============================================================================

/-- Wrap a syllable as a `SegSpec` carrying its morpheme ID. -/
def seg (s : Syll) : SegSpec Syll :=
  { seg := s, morpheme := s.morphemeId }

/-- An M tone belonging to the morpheme of syllable `s` (the lexical M
    of an /M^H/ stem). -/
def mTone (s : Syll) : ToneSpec :=
  { tone := TRN.M, morpheme := s.morphemeId }

/-- An H tone belonging to the morpheme of syllable `s` (the floating
    H of an /M^H/ stem). -/
def hTone (s : Syll) : ToneSpec :=
  { tone := TRN.H, morpheme := s.morphemeId }

/-- An L tone belonging to the morpheme of syllable `s` (the L of an
    /LH/ lexical stem like `ìlí`). -/
def lTone (s : Syll) : ToneSpec :=
  { tone := TRN.L, morpheme := s.morphemeId }

end Fragments.Poko
