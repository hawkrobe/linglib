import Linglib.Features.Prosody
import Mathlib.Data.Real.Basic

/-!
# Japanese Prosody Fragment

Word-level prosodic entries for Tokyo Japanese: lexical pitch accent as a mora
position ([beckman-pierrehumbert-1986]; [kawahara-2015]), frequency-annotated
entries and compounds ([breiss-katsuda-kawahara-2026]), and an affix lexicon
classified by the eight-way `Features.Prosody.AffixAccentType` typology
([kawahara-2015] §6).

Accent values are grounded in the sources' own data: the presence/location
minimal pairs of [kawahara-2015] (1) and (28), and the accentual-phrase
materials of [beckman-pierrehumbert-1986] (Figs. 6–13).
-/

namespace Japanese.Prosody

open Features.Prosody

/-- A Japanese lexical entry with its prosodic specification. The accent is
    the 0-indexed mora position of the linked H tone, and unaccented words
    have `accentMora = none` ([beckman-pierrehumbert-1986]). -/
structure ProsodicEntry where
  /-- Surface form (romanized) -/
  form : String
  /-- Gloss -/
  gloss : String
  /-- Mora position of the accent (`none` = unaccented) -/
  accentMora : Option ℕ
  /-- Number of morae in the word -/
  nMorae : ℕ
  deriving Repr

/-- Whether the entry bears an accent. -/
def ProsodicEntry.isAccented (e : ProsodicEntry) : Bool :=
  e.accentMora.isSome

/-! ### Sample entries

The presence-vs-absence minimal pair *ame* ~ *a'me* of [kawahara-2015] (1a–b),
and the adjective and noun materials of [beckman-pierrehumbert-1986]'s
accentual-phrase experiments (Figs. 6–13), also cited as [kawahara-2015] (28). -/

/-- *ame* 'candy' — unaccented ([kawahara-2015] (1a); the unaccented noun of
    [beckman-pierrehumbert-1986] Fig. 6). -/
def ameCandy : ProsodicEntry :=
  { form := "ame", gloss := "candy", accentMora := none, nMorae := 2 }

/-- *a'me* 'rain' — initial accent, minimal with `ameCandy`
    ([kawahara-2015] (1b)). -/
def ameRain : ProsodicEntry :=
  { form := "ame", gloss := "rain", accentMora := some 0, nMorae := 2 }

/-- *uma'i* 'delicious' — accented adjective ([kawahara-2015] (28a);
    [beckman-pierrehumbert-1986] Figs. 6, 9). -/
def umai : ProsodicEntry :=
  { form := "umai", gloss := "delicious", accentMora := some 1, nMorae := 3 }

/-- *amai* 'sweet' — unaccented adjective, minimal with `umai`
    ([kawahara-2015] (28b); [beckman-pierrehumbert-1986] Fig. 8). -/
def amai : ProsodicEntry :=
  { form := "amai", gloss := "sweet", accentMora := none, nMorae := 3 }

/-- *mame'* 'beans' — final accent ([beckman-pierrehumbert-1986] Fig. 6,
    where AP-grouping with *uma'i* deletes this accent). -/
def mame : ProsodicEntry :=
  { form := "mame", gloss := "beans", accentMora := some 1, nMorae := 2 }

theorem ameRain_accented : ameRain.isAccented = true := rfl

theorem ameCandy_unaccented : ameCandy.isAccented = false := rfl

/-! ### Frequency-annotated lexical entries -/

/-- A lexical entry carrying the two corpus annotations of
    frequency-conditioned phonology, a token log-frequency and a free/bound
    flag ([breiss-katsuda-kawahara-2026]). -/
structure LexicalEntry extends ProsodicEntry where
  /-- Token log-frequency in a reference corpus (e.g., BCCWJ). `0`
      conventionally means "log of 1 occurrence" — used as the no-info
      default for unannotated items. Stored as `ℚ` so that the lexicon
      remains computable while the abstract `Phonology/`
      interface coerces to `ℝ`. -/
  tokenLogFreq : ℚ := 0
  /-- Can this morpheme stand alone as a wordform? `false` for bound
      stems that occur only in compounds (e.g., the bound N2s targeted
      in [breiss-katsuda-kawahara-2026]). -/
  canStandAlone : Bool := true
  deriving Repr

/-- The token log-frequency as the `ℝ` value that frequency-conditioned
    phonology reads. The underlying `ℚ` field keeps the lexicon
    computable. -/
noncomputable def LexicalEntry.tokenFreq (e : LexicalEntry) : ℝ := (e.tokenLogFreq : ℝ)

/-! ### Compounds -/

/-- A Japanese N1 + N2 nominal compound. Compound-medial position is the
    locus of voiced velar nasalisation (/g/ → [ŋ]), obligatory when N2 is
    bound and otherwise frequency-conditioned
    ([breiss-katsuda-kawahara-2026]). -/
structure NominalCompound where
  n1 : LexicalEntry
  n2 : LexicalEntry
  /-- Token log-frequency of the compound *as a unit* — independent of the
      constituents' frequencies, and the principal conditioning variable on
      optional nasalisation. -/
  compoundLogFreq : ℚ := 0
  deriving Repr

/-- The compound's surface form, the concatenation of the N1 and N2 forms
    (the segmental alternation /g/ → [ŋ] applies on top). -/
def NominalCompound.form (c : NominalCompound) : String := c.n1.form ++ c.n2.form

/-- A compound's nasalisation is *obligatory* iff its N2 is bound. The
    free-N2 case is the gradient one tested in
    [breiss-katsuda-kawahara-2026]. -/
def NominalCompound.nasalisationObligatory (c : NominalCompound) : Bool :=
  ! c.n2.canStandAlone

/-! ### Affix accent lexicon

One canonical affix per accent type of [kawahara-2015] §6's eight-way
typology, encoded by `Features.Prosody.AffixAccentType`. -/

/-- A Japanese affix with its accentual behavior class. -/
structure AffixEntry where
  form : String
  gloss : String
  accentType : AffixAccentType
  deriving Repr

/-- The recessive conditional suffix *-ta'ra*, which bears accent but loses
    it to an accented root ([kawahara-2015] (29)). -/
def taraSuffix : AffixEntry :=
  { form := "-tara", gloss := "conditional", accentType := .recessive }

/-- The dominant suffix *-ppo'i* '-ish', which bears accent and deletes
    root accent ([kawahara-2015] (30)). -/
def ppoiSuffix : AffixEntry :=
  { form := "-ppoi", gloss := "-ish", accentType := .dominant }

/-- The recessive pre-accenting suffix *-si* (氏 'Mr.'), which inserts
    accent on the root-final syllable when the root is unaccented and
    preserves root accent when present ([kawahara-2015] (31)). -/
def siSuffix : AffixEntry :=
  { form := "-si", gloss := "Mr.", accentType := .recessivePreAccent }

/-- The dominant pre-accenting suffix *-ke* 'family of', which always
    inserts accent on the root-final syllable, deleting any root accent
    ([kawahara-2015] (32)). -/
def keSuffix : AffixEntry :=
  { form := "-ke", gloss := "family of", accentType := .dominantPreAccent }

/-- The accent-shifting suffix *-mono* 'thing', which shifts existing root
    accent to pre-suffix position but never creates new accent
    ([kawahara-2015] (33)). -/
def monoSuffix : AffixEntry :=
  { form := "-mono", gloss := "thing", accentType := .accentShifting }

/-- The post-accenting honorific prefix *o-*, which inserts accent after
    the prefix ([kawahara-2015] (34)). -/
def oPrefix : AffixEntry :=
  { form := "o-", gloss := "honorific", accentType := .postAccenting }

/-- The deaccenting suffix *-teki* (的 '-like'), which deletes root accent
    and inserts none ([kawahara-2015] (36)). -/
def tekiSuffix : AffixEntry :=
  { form := "-teki", gloss := "的 -like", accentType := .deaccenting }

/-- The initial-accenting suffix *-zu* of group names, which inserts accent
    on the root-initial syllable ([kawahara-2015] (39)). -/
def zuSuffix : AffixEntry :=
  { form := "-zu", gloss := "group", accentType := .initialAccenting }

end Japanese.Prosody
