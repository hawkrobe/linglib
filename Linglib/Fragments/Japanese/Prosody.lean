import Linglib.Core.Prosody
import Linglib.Phenomena.Intonation.Studies.BeckmanPierrehumbert1986

/-!
# Japanese Prosody Fragment
@cite{beckman-pierrehumbert-1986}

Japanese prosodic entries following the autosegmental-metrical analysis
of @cite{beckman-pierrehumbert-1986}.

## Key Properties

- **Lexical accent**: accent location specified in the lexicon as a linked
  H tone. The accent shape is fixed (H*+L); only the location varies.
- **Accented vs unaccented**: some words are lexically unaccented (e.g.,
  compound nouns formed from unaccented words). Unaccented words can
  form well-formed utterances without any pitch accent.
- **Accentual phrase**: delimited by a phrasal H (on the second sonorant
  mora) and a boundary L. Contains at most one accent.
- **Sparse tonal specification**: only the accent H, the phrasal H, and
  the boundary L are specified; F0 between them is interpolated.
-/

namespace Fragments.Japanese.Prosody

open Core.Prosody
open Phenomena.Intonation.Studies.BeckmanPierrehumbert1986

-- ============================================================================
-- § 1: Lexical Accent
-- ============================================================================

/-- A Japanese lexical entry with prosodic specification.

    The accent is specified as the mora position of the linked H tone
    (0-indexed from the beginning of the word). Unaccented words have
    `accentMora = none`. -/
structure JProsodicEntry where
  /-- Surface form (romanized) -/
  form : String
  /-- Gloss -/
  gloss : String
  /-- Mora position of the accent (none = unaccented) -/
  accentMora : Option Nat
  /-- Number of morae in the word -/
  nMorae : Nat
  deriving Repr

/-- Is this entry accented? -/
def JProsodicEntry.isAccented (e : JProsodicEntry) : Bool :=
  e.accentMora.isSome

/-- Convert to Bool accentedness for bridge to AccentualPhrase. -/
def JProsodicEntry.accentedBool (e : JProsodicEntry) : Bool :=
  e.isAccented

-- ============================================================================
-- § 2: Sample Entries (§2.1, §2.2)
-- ============================================================================

/-- *kami* 'god' — accented on first mora (initial accent).
    Contrasts with *kami* 'paper' (unaccented) and *kamí* 'hair'
    (accent on second mora). -/
def kami_god : JProsodicEntry :=
  { form := "kami", gloss := "god", accentMora := some 0, nMorae := 2 }

/-- *kami* 'paper' — unaccented.
    No HL fall in the accentual phrase. -/
def kami_paper : JProsodicEntry :=
  { form := "kami", gloss := "paper", accentMora := none, nMorae := 2 }

/-- *uma'i* — accented adjective (§2.2, Figs. 6, 8, 9). -/
def umai : JProsodicEntry :=
  { form := "umai", gloss := "delicious", accentMora := some 1, nMorae := 3 }

/-- *amai* — accented adjective (§2.3, Fig. 8). -/
def amai : JProsodicEntry :=
  { form := "amai", gloss := "sweet", accentMora := some 1, nMorae := 3 }

/-- *mame* — unaccented noun (§2.2, Fig. 6). -/
def mame : JProsodicEntry :=
  { form := "mame", gloss := "beans", accentMora := none, nMorae := 2 }

/-- *ame* — unaccented noun (§2.2, Fig. 6). -/
def ame : JProsodicEntry :=
  { form := "ame", gloss := "rain", accentMora := none, nMorae := 2 }

-- ============================================================================
-- § 3: Accentual Phrase Structure (§2.2)
-- ============================================================================

/-- Japanese accentual phrase tonal specification.

    @cite{beckman-pierrehumbert-1986} §2.2: the AP is defined by:
    - A boundary L at the beginning (or end of preceding AP)
    - A phrasal H on the second sonorant mora
    - An optional accent HL (if the word is accented)
    - A boundary L at the end

    The phrasal H is NOT the same as H-tone spreading from the accent;
    it has its own local pitch range and is always present, even in
    unaccented phrases (Fig. 3 vs earlier accounts). -/
structure JAccentualPhrase where
  /-- Words grouped in this AP -/
  words : List JProsodicEntry
  /-- Whether the phrasal H is present (always true in Japanese) -/
  hasPhrasalH : Bool := true
  deriving Repr

/-- An AP is accented if any word in it is accented. -/
def JAccentualPhrase.isAccented (ap : JAccentualPhrase) : Bool :=
  ap.words.any (·.isAccented)

/-- Convert to the generic AccentualPhrase type.
    Japanese accent shape is always H*+L; unaccented APs get null. -/
def JAccentualPhrase.toGeneric (ap : JAccentualPhrase) : AccentualPhrase :=
  { accent := if ap.isAccented then .H_star_plus_L else .null
    nWords := ap.words.length }

-- ============================================================================
-- § 4: Verification
-- ============================================================================

/-- Accented words have accent location. -/
theorem kami_god_accented : kami_god.isAccented = true := rfl

/-- Unaccented words lack accent location. -/
theorem kami_paper_unaccented : kami_paper.isAccented = false := rfl

/-- Japanese accent is lexical. -/
theorem japanese_accent_is_lexical :
    (Phenomena.Intonation.Studies.BeckmanPierrehumbert1986.japanese).accentSpec
    = .lexical := rfl

/-- The Japanese pitch accent shape is H*+L (a single bitonal accent). -/
theorem japanese_accent_is_bitonal :
    PitchAccent.H_star_plus_L.isBitonal = true := rfl

/-- A Japanese accented AP always triggers catathesis (because H*+L is bitonal). -/
theorem japanese_accented_ap_triggers_catathesis (ap : JAccentualPhrase)
    (h : ap.isAccented = true) :
    ap.toGeneric.accent.isBitonal = true := by
  unfold JAccentualPhrase.toGeneric; rw [if_pos h]; rfl

/-- A Japanese unaccented AP never triggers catathesis. -/
theorem japanese_unaccented_ap_no_catathesis (ap : JAccentualPhrase)
    (h : ap.isAccented = false) :
    ap.toGeneric.accent.isBitonal = false := by
  unfold JAccentualPhrase.toGeneric; rw [if_neg (by simp [h])]; rfl

/-- An AP containing only unaccented words is unaccented. -/
theorem unaccented_ap :
    ({ words := [kami_paper, mame] : JAccentualPhrase }).isAccented = false := rfl

/-- An AP containing an accented word is accented. -/
theorem accented_ap :
    ({ words := [kami_god, mame] : JAccentualPhrase }).isAccented = true := rfl

-- ============================================================================
-- § 5: Suffix Prosodic Dominance (@cite{kawahara-2015})
-- ============================================================================

/-- Japanese suffix accent specification.

    Japanese suffixes exhibit the same dominant/recessive distinction
    as IE accent systems (@cite{kiparsky-halle-1977}) and GT systems
    (@cite{rolle-2018}). Dominant suffixes remove stem accent;
    recessive suffixes preserve it when present. -/
structure JSuffixAccent where
  form : String
  gloss : String
  dominance : Core.Prosody.ProsodicDominance
  deriving Repr

/-- *-teki* (的): deaccenting suffix. Removes stem accent regardless
    of whether the stem is accented or unaccented — classified as
    subtractive-dominant in GT terms (@cite{kawahara-2015}). -/
def teki_suffix : JSuffixAccent :=
  { form := "-teki", gloss := "的 ADJ", dominance := .dominant }

/-- *-si* (氏): non-deaccenting suffix. Preserves stem accent when
    present — classified as recessive (@cite{kawahara-2015}). -/
def si_suffix : JSuffixAccent :=
  { form := "-si", gloss := "氏 Mr.", dominance := .recessive }

/-- Deaccenting suffixes are dominant. -/
theorem teki_is_dominant : teki_suffix.dominance.isDominant = true := rfl

/-- Non-deaccenting suffixes are not dominant. -/
theorem si_is_not_dominant : si_suffix.dominance.isDominant = false := rfl

-- ============================================================================
-- § 6: Accent Combination (@cite{kawahara-2015})
-- ============================================================================

/-- Derive the accent of a suffixed word from stem accent + suffix dominance. -/
def suffixedAccent (stem : JProsodicEntry) (suffix : JSuffixAccent) : Option Nat :=
  suffix.dominance.combineAccent stem.accentMora

/-- *-teki* deaccents *kami* 'god' (accented). -/
theorem teki_deaccents_kami_god :
    suffixedAccent kami_god teki_suffix = none := rfl

/-- *-teki* leaves *kami* 'paper' (unaccented) unchanged. -/
theorem teki_leaves_kami_paper :
    suffixedAccent kami_paper teki_suffix = none := rfl

/-- *-teki* neutralizes the *kami* 'god' / *kami* 'paper' contrast. -/
theorem teki_neutralizes_kami :
    suffixedAccent kami_god teki_suffix =
    suffixedAccent kami_paper teki_suffix := rfl

/-- *-si* preserves the accent on *kami* 'god'. -/
theorem si_preserves_kami_god :
    suffixedAccent kami_god si_suffix = some 0 := rfl

/-- *-si* preserves the unaccentedness of *kami* 'paper'. -/
theorem si_preserves_kami_paper :
    suffixedAccent kami_paper si_suffix = none := rfl

/-- *-si* maintains the *kami* 'god' / *kami* 'paper' contrast. -/
theorem si_maintains_kami_contrast :
    suffixedAccent kami_god si_suffix ≠
    suffixedAccent kami_paper si_suffix := by decide

end Fragments.Japanese.Prosody
