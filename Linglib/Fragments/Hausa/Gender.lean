import Linglib.Features.Gender.Basic

/-!
# Hausa Gender Fragment
[newman-2000] [corbett-1991] [kramer-2020]

Hausa (Chadic, Afroasiatic) has a two-gender system: masculine and
feminine, with -ā as a frequent (but neither necessary nor sufficient)
correlate of feminine gender.

## Theory-neutral data layer

The Fragment commits to two empirical fields per entry:

- `attestedGender : Gender` — the agreement-trigger fact
  (which gender determiners, possessive linkers, TAM clitics, and
  pronouns realize when referring to this noun). Verified against
  [newman-2000] Ch. 31 (pp. 201–215).
- `isNaturalGender : Bool` — whether the gender is semantically
  motivated by the referent's biological sex (or the lexicalized
  sex distinction in cases like *kāzā* 'hen' / *zàkarā* 'rooster').
  Newman/Corbett/Kramer all agree on this empirical field.

These two fields suffice to project every entry's structural analysis
under a Set-1 DM categorizer (see `Studies/Kramer2020.lean`
for the projection); they also suffice for Newman-style and Corbett-style
analyses that don't go through DM at all.

## Empirical baseline ([newman-2000] Ch. 31)

- p. 201: lexical-gender lists for each entry verified.
- p. 208 footnote [i]: *mācè* 'woman' is feminine but does NOT end in
  *-ā* — Newman's canonical exception, derived from *mātā* via a
  process that lost -ā.
- p. 209: 250+ ā-final masculines out of ~3000, partitioned into
  (a) Native (e.g. *kadā* 'crocodile', *ùbā* 'father', *zàkarā* 'rooster'),
  (b) Loanwords, (c) Erstwhile plurals (e.g. *gidā* 'house', *karā*
  'cornstalk', *ruwā* 'water'). Both *kadā* and *gidā* in this Fragment
  are masculine but in distinct historical classes.
- p. 213: Newman's "overt characterization" theory — synchronically
  the {-ā} suffix is a morphological feminine marker (not a phonological
  rule); diachronically, feminine nouns acquired -ā via overt
  characterization ([newman-1979a]).

## Theoretical framings (deferred to Studies/)

[corbett-1991] §3.2.2 (pp. 52–53): synchronic phonological
assignment with exceptions. Diachronic origin in §4.5 (pp. 102–103).

[kramer-2020] §3.3.1 (pp. 60–61): morphophonological *realization*
of [+FEM] on n, NOT phonological *assignment*. Aligns with Newman's
synchronic view.

The cross-framework theorems live in `Studies/Kramer2020.lean`.
Spanish/Russian/German Fragment Gender files still bake in DM `CatHead`
fields; Hausa is the pilot for theory-neutral Fragment-layer encoding.
-/

namespace Hausa


/-- A Hausa noun: surface form, gloss, and two empirical gender fields.
    No commitment to any specific theoretical framework — the DM
    categorizer head, Corbett's controller-target classification, etc.
    are projections that live in `Studies/`. -/
structure Noun where
  form : String
  gloss : String
  /-- The agreement-trigger fact: what gender does this noun realize
      on agreeing elements (determiners, pronouns, TAM clitics)?
      Verified against [newman-2000] Ch. 31. -/
  attestedGender : Gender
  /-- True iff the gender is semantically motivated by the referent's
      biological sex (humans, sex-paired animals like *kāzā/zàkarā*).
      False for inanimates and unsexed animals. -/
  isNaturalGender : Bool
  deriving DecidableEq, Repr

namespace Noun

/-- The noun's surface gender — the agreement-trigger fact stored
    directly in the entry. Alias for `attestedGender` to make
    `n.gender` read naturally at consumer sites. -/
abbrev gender (n : Noun) : Gender := n.attestedGender

/-- The *-ā* suffix diagnostic. Tone-tolerant: a trailing combining
    diacritic (e.g. low-tone grave on *kadā̀*) does not block the match,
    so the predicate captures the linguistic notion "ends in long *-ā*"
    rather than the orthographic notion "last codepoint is U+0101". We
    test membership in the last two characters of the surface form's
    `toList`; this admits an optional trailing combining mark without
    risking false positives for our entries (`mācè`, `littāfī`, `yārō`,
    `mùtûm` all correctly fail). We work on the character list rather
    than `String.endsWith` because the latter does not reduce in the
    kernel. -/
abbrev EndsInAa (n : Noun) : Prop :=
  'ā' ∈ n.form.toList.reverse.take 2

end Noun

-- Lexical entries. Transcriptions follow [newman-2000] Ch. 31
-- (macron = long vowel, grave = low tone, circumflex = falling tone,
-- ƙ = ejective velar). Each entry is verified against Newman's gender
-- lists on pp. 201, 208–209, 213.

def yarinya  : Noun := ⟨"yārinyā", "girl",     .feminine,  true⟩
/-- *mācè* 'woman' — feminine despite NOT ending in *-ā*.
    [newman-2000] p. 208 footnote [i] explicitly flags *mācè* as
    the canonical exception: feminine but ends in -è. Newman: *mācè*
    is historically a derived form ('female') from *mātā* 'woman/wife'
    that lost -ā; only later became a common noun. -/
def mace     : Noun := ⟨"mācè",    "woman",    .feminine,  true⟩
/-- *kāzā* 'hen' — natural feminine. [newman-2000] p. 201 lists
    *kāzā* in the natural-gender feminine pair with *zàkarā* 'rooster'.
    Sex distinction is lexicalized (separate words for hen/rooster), so
    natural per Newman + per Kramer's "honoris causa" criterion
    ([kramer-2020] p. 57). -/
def kaza     : Noun := ⟨"kāzā",    "hen",      .feminine,  true⟩
def riga     : Noun := ⟨"rīgā",    "gown",     .feminine,  false⟩
def yaro     : Noun := ⟨"yārō",    "boy",      .masculine, true⟩
def mutum    : Noun := ⟨"mùtûm",   "man",      .masculine, true⟩
def littafi  : Noun := ⟨"littāfī", "book",     .masculine, false⟩
/-- *gidā* 'house' — masculine despite ending in *-ā*.
    [newman-2000] p. 209 class (c) "Erstwhile plurals" (alongside
    *karā* 'cornstalk', *ƙudā* 'housefly', *ruwā* 'water'): historically
    plural forms now used as singulars. Distinct historical class from
    the native ā-final masculines (kadā, ubā, zàkarā). -/
def gida     : Noun := ⟨"gidā",    "house",    .masculine, false⟩
def kasaLand : Noun := ⟨"ƙasā",    "land",     .feminine,  false⟩
def rana     : Noun := ⟨"rānā",    "sun/day",  .feminine,  false⟩
/-- *kadā̀* 'crocodile' — masculine despite ending in *-ā*.
    [newman-2000] p. 209 class (a) "Native" ā-final masculines.
    [kramer-2020] ex. 22e (p. 55) cites this from Newman as the
    canonical counterexample to phonological assignment. -/
def kada     : Noun := ⟨"kadā̀",   "crocodile", .masculine, false⟩
/-- *ùbā* 'father' — natural masculine ending in *-ā*.
    [newman-2000] p. 209 class (a) "Native" ā-final masculines.
    [kramer-2015] Ch. 1 cites this as one of two introductory
    Hausa examples (alongside *sāfīyā* 'morning.f') from
    [newman-2000] p. 201. Doubles as a natural-gender masculine
    AND a masculine -ā witness — refutes phonological assignment from a
    different angle than *kadā̀* (which is non-natural): even
    semantically male-denoting nouns in Hausa can end in -ā. -/
def uba      : Noun := ⟨"ùbā",     "father",   .masculine, true⟩

def allNouns : List Noun :=
  [yarinya, mace, kaza, riga, yaro, mutum, littafi, gida,
   kasaLand, rana, kada, uba]

end Hausa
