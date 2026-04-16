import Linglib.Core.Prosody
import Linglib.Theories.Phonology.Accent
import Linglib.Phenomena.Intonation.Studies.BeckmanPierrehumbert1986

/-!
# Japanese Prosody Fragment
@cite{beckman-pierrehumbert-1986} @cite{kawahara-2015}

Japanese prosodic entries following the autosegmental-metrical analysis
of @cite{beckman-pierrehumbert-1986}, with accent assignment rules and
affix typology from @cite{kawahara-2015}.

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
- **Culminativity**: at most one HL fall per prosodic word — Japanese is
  a pitch-accent language, not a tone language.
- **Default accent**: loanwords and nonce words receive antepenultimate
  accent (AAR) or Latin Stress Rule (LSR) accent.
- **Eight affix accent types**: recessive, dominant, recessive
  pre-accenting, dominant pre-accenting, accent-shifting,
  post-accenting, deaccenting, initial-accenting.
-/

namespace Fragments.Japanese.Prosody

open Core.Prosody
open Phonology.Accent (defaultAccentAAR latinStressRule accentToTones
  LevelTone shortN2CompoundAccent longN2CompoundAccent)
open Phonology.Syllable (SyllWeight)
open BeckmanPierrehumbert1986

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
    (BeckmanPierrehumbert1986.japanese).accentSpec
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

-- ============================================================================
-- § 7: Loanword Entries (@cite{kawahara-2015} §2)
-- ============================================================================

/-- Loanword prosodic entry. Extends `JProsodicEntry` with syllable weight
    profile for testing AAR vs LSR predictions. -/
structure JLoanwordEntry where
  entry : JProsodicEntry
  /-- Syllable weight profile (left to right) -/
  weights : List SyllWeight
  deriving Repr

/-- *kurisumasu* 'Christmas' — accent on antepenultimate mora (su).
    @cite{kawahara-2015} (10a). -/
def kurisumasu : JLoanwordEntry :=
  { entry := { form := "kurisumasu", gloss := "Christmas"
               accentMora := some 2, nMorae := 5 }
    weights := [.light, .light, .light, .light, .light] }

/-- *asufaruto* 'asphalt' — accent on antepenultimate mora (fa).
    @cite{kawahara-2015} (10g). -/
def asufaruto : JLoanwordEntry :=
  { entry := { form := "asufaruto", gloss := "asphalt"
               accentMora := some 2, nMorae := 5 }
    weights := [.light, .light, .light, .light, .light] }

/-- *makudonarudo* 'McDonald' — accent on antepenultimate mora (na).
    @cite{kawahara-2015} (10h). -/
def makudonarudo : JLoanwordEntry :=
  { entry := { form := "makudonarudo", gloss := "McDonald's"
               accentMora := some 4, nMorae := 7 }
    weights := [.light, .light, .light, .light, .light, .light, .light] }

/-- *amerika* 'America' — unaccented (4-mora with two final light σ).
    @cite{kawahara-2015} (16a). -/
def amerika : JLoanwordEntry :=
  { entry := { form := "amerika", gloss := "America"
               accentMora := none, nMorae := 4 }
    weights := [.light, .light, .light, .light] }

/-- Loanword accent matches AAR prediction for all-light syllables. -/
theorem kurisumasu_matches_aar :
    defaultAccentAAR kurisumasu.weights = kurisumasu.entry.accentMora := rfl

/-- Loanword accent matches LSR prediction for all-light syllables. -/
theorem kurisumasu_matches_lsr :
    latinStressRule kurisumasu.weights = kurisumasu.entry.accentMora := by
  unfold latinStressRule; unfold latinStressRule; unfold latinStressRule; rfl

-- ============================================================================
-- § 8: AAR vs LSR Mismatch Cases (@cite{kawahara-2015} Table 1)
-- ============================================================================

/-- HLH: AAR predicts penultimate (σ₂), LSR predicts antepenultimate (σ₁).
    @cite{kawahara-2015} Table 1, row (c). -/
theorem aar_lsr_mismatch_hlh :
    defaultAccentAAR [.heavy, .light, .heavy] = some 1 ∧
    latinStressRule [.heavy, .light, .heavy] = some 0 := by
  constructor <;> (first | rfl | (unfold latinStressRule; rfl))

/-- LLH: AAR predicts penultimate (σ₂), LSR predicts antepenultimate (σ₁).
    @cite{kawahara-2015} Table 1, row (g). -/
theorem aar_lsr_mismatch_llh :
    defaultAccentAAR [.light, .light, .heavy] = some 1 ∧
    latinStressRule [.light, .light, .heavy] = some 0 := by
  constructor <;> (first | rfl | (unfold latinStressRule; rfl))

/-- The remaining 6 conditions in Table 1 produce matching predictions. -/
theorem aar_lsr_match_hhh :
    defaultAccentAAR [.heavy, .heavy, .heavy] =
    latinStressRule [.heavy, .heavy, .heavy] := by unfold latinStressRule; rfl
theorem aar_lsr_match_hhl :
    defaultAccentAAR [.heavy, .heavy, .light] =
    latinStressRule [.heavy, .heavy, .light] := by unfold latinStressRule; rfl
theorem aar_lsr_match_hll :
    defaultAccentAAR [.heavy, .light, .light] =
    latinStressRule [.heavy, .light, .light] := by unfold latinStressRule; rfl
theorem aar_lsr_match_lhh :
    defaultAccentAAR [.light, .heavy, .heavy] =
    latinStressRule [.light, .heavy, .heavy] := by unfold latinStressRule; rfl
theorem aar_lsr_match_lhl :
    defaultAccentAAR [.light, .heavy, .light] =
    latinStressRule [.light, .heavy, .light] := by unfold latinStressRule; rfl
theorem aar_lsr_match_lll :
    defaultAccentAAR [.light, .light, .light] =
    latinStressRule [.light, .light, .light] := by unfold latinStressRule; rfl

-- ============================================================================
-- § 9: Fine-Grained Affix Accent Typology (@cite{kawahara-2015} §6)
-- ============================================================================

/-- Japanese suffix with fine-grained accent classification. -/
structure JAffixEntry where
  form : String
  gloss : String
  accentType : AffixAccentType
  deriving Repr

-- The eight affix types with canonical examples from Kawahara (2015):

/-- *-tara* (conditional): recessive suffix — bears accent, loses to root.
    @cite{kawahara-2015} (29). -/
def tara_suffix : JAffixEntry :=
  { form := "-tara", gloss := "conditional", accentType := .recessive }

/-- *-ppoi* (-ish): dominant suffix — bears accent, overrides root.
    @cite{kawahara-2015} (30). -/
def ppoi_suffix : JAffixEntry :=
  { form := "-ppoi", gloss := "-ish", accentType := .dominant }

/-- *-si* (Mr.): recessive pre-accenting — inserts accent on root-final σ
    when root is unaccented, preserves root accent when present.
    @cite{kawahara-2015} (31). -/
def si_affix : JAffixEntry :=
  { form := "-si", gloss := "Mr.", accentType := .recessivePreAccent }

/-- *-ke* (family of): dominant pre-accenting — always inserts accent on
    root-final σ, deleting any root accent.
    @cite{kawahara-2015} (32). -/
def ke_suffix : JAffixEntry :=
  { form := "-ke", gloss := "family of", accentType := .dominantPreAccent }

/-- *-mono* (thing): accent-shifting — shifts existing root accent to
    pre-suffix position. Unaccented roots stay unaccented.
    @cite{kawahara-2015} (33). -/
def mono_suffix : JAffixEntry :=
  { form := "-mono", gloss := "thing", accentType := .accentShifting }

/-- *o-* (honorific prefix): post-accenting — inserts accent after prefix.
    @cite{kawahara-2015} (34). -/
def o_prefix : JAffixEntry :=
  { form := "o-", gloss := "honorific", accentType := .postAccenting }

/-- *-teki* (的 -like): deaccenting — deletes root accent, no new accent.
    @cite{kawahara-2015} (36). -/
def teki_affix : JAffixEntry :=
  { form := "-teki", gloss := "的 -like", accentType := .deaccenting }

/-- *-zu* (group/plural): initial-accenting — inserts accent on root-initial σ.
    @cite{kawahara-2015} (39). -/
def zu_suffix : JAffixEntry :=
  { form := "-zu", gloss := "group", accentType := .initialAccenting }

-- Classification theorems: the 8 types project correctly to the
-- coarser dominant/recessive distinction.

/-- Recessive pre-accenting is recessive at the coarse level
    (preserves root accent when present). -/
theorem si_is_recessive_coarse :
    si_affix.accentType.toProsodicDominance = .recessive := rfl

/-- Deaccenting is dominant at the coarse level (overrides root accent).
    This corrects the earlier classification of *-teki* in this fragment,
    which used `ProsodicDominance.dominant` — functionally the same
    projection, but the fine-grained type makes the behavior explicit. -/
theorem teki_is_dominant_coarse :
    teki_affix.accentType.toProsodicDominance = .dominant := rfl

/-- Accent-shifting is recessive at the coarse level: it only operates
    on accent that is already present, never creating new accent. -/
theorem mono_is_recessive_coarse :
    mono_suffix.accentType.toProsodicDominance = .recessive := rfl

-- ============================================================================
-- § 10: Compound Accent (@cite{kawahara-2015} §4)
-- ============================================================================

/-- *kabuto+musi* 'beetle': short N2 (*musi*, 2μ) pre-accents on
    N1-final syllable. @cite{kawahara-2015} (22a). -/
theorem kabuto_musi_compound :
    shortN2CompoundAccent 3 (some 0) true = some 2 := rfl

/-- *sin+yokohama* 'Shin-Yokohama': long N2 (*yokohama*, 4μ, unaccented)
    → accent on N2-initial syllable. @cite{kawahara-2015} (23a). -/
theorem sin_yokohama_compound :
    longN2CompoundAccent 2 none 4 = some 2 := rfl

/-- *sin+tamane'gi* 'new onion': long N2 retains accent.
    @cite{kawahara-2015} (24a). -/
theorem sin_tamanegi_compound :
    longN2CompoundAccent 2 (some 2) 4 = some 4 := rfl

-- ============================================================================
-- § 11: Accent-to-Tone Verification (@cite{kawahara-2015} §1.4)
-- ============================================================================

/-- Unaccented trisyllable *ame+ga* → LHH (initial rise + H spread). -/
theorem ame_ga_tones :
    accentToTones ame.accentMora 3 = [.L, .H, .H] := rfl

/-- Accented *ka'mi+ga* → HLL (accent HL + L spread). -/
theorem kami_god_ga_tones :
    accentToTones kami_god.accentMora 3 = [.H, .L, .L] := rfl

end Fragments.Japanese.Prosody
