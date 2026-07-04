import Linglib.Phonology.Tone.Basic
import Linglib.Phonology.Autosegmental.Floating

/-!
# Poko Tonal Fragment

Lexical tone data for Poko (Poko-Rawo; Glottolog `rawo1244`, ISO 639-3
`rwa`), a Skou language of Sandaun Province, Papua New Guinea (~100
speakers, [mcpherson-dryer-2021]). Three contrastive tone levels (H,
M, L) plus toneless syllables and floating tones; the TBU is the
syllable. Lexical melodies span `Ø`, `M`, `MH`, `LM`, `LH`, `M^H` and
double-floating `^L∅^H`, with floating L only stem-initial and
floating H only stem-final ([mcpherson-lamont-2026] ex. 3, §2.2);
simple `L` and `H` melodies are absent — [mcpherson-2022] derives the
gap from edge constraints (`NonInitial(H)`, `NonFinal(L)`), while
[mcpherson-lamont-2026] speculate an extreme OCP response.

Just enough stems for the [mcpherson-lamont-2026] tableaux; promote to
a fuller fragment when a second Poko paper arrives.

## Main definitions

* `Poko.Syll` — the stems, one morpheme each (`Syll.morpheme`).
* `Poko.Syll.melody` — lexical melody as ordered tier elements.
* `Poko.seg`, `Poko.mTone`, `Poko.hTone`, `Poko.lTone` — `SegSpec` /
  `TierSpec` builders carrying the morpheme membership that feeds
  `*TAUTDOCK` and `*CROWD`.
* `Poko.Form` — autosegmental forms (`FloatingForm Syll TRN`).
-/

namespace Poko

open Autosegmental
open Tone (TRN)

/-! ### Syllables -/

/-- Poko syllables for the [mcpherson-lamont-2026] tableaux: fig. 3
    (`kak`, `ri`, `do`); eq. (24) (`nan`, `ri`, `na`); eq. (27)
    (`kak`, `ka`); eq. (30) (`kak`, `ili`); eq. (22a) (`ne`). -/
inductive Syll
  /-- 3sg.m possessive `kāk` (melody `/M^H/`). -/
  | kak
  /-- Pig stem `rī` (melody `/M^H/`). -/
  | ri
  /-- Get verb `dō` (melody `/M^H/`). -/
  | do
  /-- 1sg pronoun `nãn` — possessor 'my' and subject 'I' (melody `/M/`). -/
  | nan
  /-- Eat verb `nã` (melody `/M/`). -/
  | na
  /-- Friend stem `kǎ` (melody `/MH/`, surfacing as a rise; eq. 26a). -/
  | ka
  /-- Bamboo stem `ìlí` (melody `/LH/`; disyllabic in the language,
      collapsed to a single backbone element here; eq. 28a). -/
  | ili
  /-- Make.1sg verb stem `ne` (toneless; eq. 22a). -/
  | ne
  deriving DecidableEq, Repr

/-! ### Morphemes -/

/-- Stable morpheme per stem, keyed by the syllable's surface form. -/
def Syll.morpheme : Syll → Morpheme
  | .kak => { form := "kak" }
  | .ri  => { form := "ri" }
  | .do  => { form := "do" }
  | .nan => { form := "nan" }
  | .na  => { form := "na" }
  | .ka  => { form := "ka" }
  | .ili => { form := "ili" }
  | .ne  => { form := "ne" }

/-! ### Builders -/

/-- Wrap a syllable as a `SegSpec` carrying its morpheme. -/
def seg (s : Syll) : SegSpec Syll :=
  { seg := s, morpheme := s.morpheme }

/-- An M tone belonging to the morpheme of syllable `s`. -/
def mTone (s : Syll) : TierSpec TRN :=
  { value := TRN.M, morpheme := s.morpheme }

/-- An H tone belonging to the morpheme of syllable `s`. -/
def hTone (s : Syll) : TierSpec TRN :=
  { value := TRN.H, morpheme := s.morpheme }

/-- An L tone belonging to the morpheme of syllable `s`. -/
def lTone (s : Syll) : TierSpec TRN :=
  { value := TRN.L, morpheme := s.morpheme }

/-! ### Melodies and forms -/

/-- Lexical melody of each stem, in tier order (linked tones before a
    floating H). Which tones are underlyingly linked is per-input data
    — the `links` argument of `FloatingForm.mkInput`. -/
def Syll.melody : Syll → List (TierSpec TRN)
  | .kak => [mTone .kak, hTone .kak]  -- /M^H/
  | .ri  => [mTone .ri, hTone .ri]    -- /M^H/
  | .do  => [mTone .do, hTone .do]    -- /M^H/
  | .nan => [mTone .nan]              -- /M/
  | .na  => [mTone .na]               -- /M/
  | .ka  => [mTone .ka, hTone .ka]    -- /MH/, both linked
  | .ili => [lTone .ili, hTone .ili]  -- /LH/, both linked
  | .ne  => []                        -- toneless

/-- Poko autosegmental forms: syllable backbone, `TRN` tone tier. -/
abbrev Form := FloatingForm Syll TRN

end Poko
