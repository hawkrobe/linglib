import Linglib.Phonology.Tone.Basic
import Linglib.Phonology.Tone.Grammatical
import Linglib.Phonology.Autosegmental.Floating

/-!
# Poko Phonological Fragment — Tonal
[mcpherson-dryer-2021] [mcpherson-2022] [mcpherson-lamont-2026]

Poko (also Poko-Rawo, ISO 639-3: not assigned, Glottocode: poko1259) is
a Skou language spoken in Sandaun Province, Papua New Guinea, near the
border with West Papua. ~100 speakers as of [mcpherson-dryer-2021].

## Tone system

Three contrastive tone levels — high (H), mid (M), low (L) — plus
toneless syllables and floating tones. Lexical melodies range from `Ø`
(toneless) through `M`, `MH`, `LM`, `LH`, `M^H` (M with floating H);
[mcpherson-2022] argues the lexical inventory excludes simple `L`
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

Just enough syllables for the [mcpherson-lamont-2026] fig. 3
demonstration: `kāk` (3sg.m possessive), `rī` (pig stem with `/M^H/`
melody), `dō` (get verb with `/M^H/` melody). Promote to a fuller
fragment when a second Poko paper arrives.

## Morphemes

Each Poko stem is one morpheme, keyed by the syllable's surface form
via `Syll.morphemeId` (`{ form := "kak" }`, `{ form := "ri" }`, etc.).
Consumed by *TAUTDOCK and *CROWD via the `SegSpec`/`TierSpec TRN` morpheme
fields.
-/

namespace Poko

open Phonology.Autosegmental
open Tone (TRN)

-- ============================================================================
-- § 1: Syllables
-- ============================================================================

/-- Poko syllables represented for the [mcpherson-lamont-2026]
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

/-- Stable morpheme per stem, keyed by the syllable's surface form. -/
def Syll.morphemeId : Syll → Morpheme
  | .kak => { form := "kak" }
  | .ri  => { form := "ri" }
  | .do  => { form := "do" }
  | .nan => { form := "nan" }
  | .na  => { form := "na" }
  | .ka  => { form := "ka" }
  | .ili => { form := "ili" }
  | .ne  => { form := "ne" }

-- ============================================================================
-- § 3: Convenience Constructors for SegSpec / TierSpec TRN
-- ============================================================================

/-- Wrap a syllable as a `SegSpec` carrying its morpheme ID. -/
def seg (s : Syll) : SegSpec Syll :=
  { seg := s, morpheme := s.morphemeId }

/-- An M tone belonging to the morpheme of syllable `s` (the lexical M
    of an /M^H/ stem). -/
def mTone (s : Syll) : TierSpec TRN :=
  { value := TRN.M, morpheme := s.morphemeId }

/-- An H tone belonging to the morpheme of syllable `s` (the floating
    H of an /M^H/ stem). -/
def hTone (s : Syll) : TierSpec TRN :=
  { value := TRN.H, morpheme := s.morphemeId }

/-- An L tone belonging to the morpheme of syllable `s` (the L of an
    /LH/ lexical stem like `ìlí`). -/
def lTone (s : Syll) : TierSpec TRN :=
  { value := TRN.L, morpheme := s.morphemeId }

end Poko
