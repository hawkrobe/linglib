import Linglib.Features.Prosody

/-!
# Japanese Prosody Fragment

Word-level prosodic entries for Tokyo Japanese: lexical pitch accent as a mora
position ([beckman-pierrehumbert-1986]; [kawahara-2015]) and an affix lexicon
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
