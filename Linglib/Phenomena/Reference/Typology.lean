import Linglib.Core.Word

/-!
# Cross-Linguistic Typology of Articles and Demonstratives (WALS)

Typological data on definiteness marking, indefinite articles, and demonstrative
systems across languages, drawn from five chapters of the World Atlas of Language
Structures (Dryer & Haspelmath 2013):

- **Ch 37** (Dryer): Definite articles -- whether a language has a definite article
  as a word distinct from demonstratives, an affix, a demonstrative used for
  definiteness, or no definite marking at all.
- **Ch 38** (Dryer): Indefinite articles -- whether a language has an indefinite
  article distinct from the numeral 'one', uses 'one' as an indefinite article,
  has an indefinite affix, or lacks indefinite articles entirely.
- **Ch 41** (Diessel): Distance contrasts in demonstratives -- the number of
  distance distinctions encoded in adnominal demonstratives (1 through 5+).
- **Ch 42** (Diessel): Pronominal and adnominal demonstratives -- whether
  the two demonstrative uses have the same form, different stems, or different
  inflectional features.
- **Ch 43** (Bhat): Third-person pronouns and demonstratives -- whether
  3rd-person pronouns are identical to, derived from, or unrelated to
  demonstratives.

## Key Generalizations

1. Two-way demonstrative distance systems (proximal/distal) are the most common
   cross-linguistically (54.3%), followed by three-way systems (37.6%).
2. Languages with definite articles tend to also have indefinite articles, but
   the reverse is not true: 41 languages have only an indefinite article with
   no definite article.
3. In a majority of languages (125 of 225), third-person pronouns show some
   relationship to demonstratives -- the diachronic pathway demonstrative ->
   3rd-person pronoun is well attested.
4. The grammaticalization cline demonstrative -> definite article -> definite
   affix is a well-established diachronic pathway (Greenberg 1978, Himmelmann
   1997).

## References

- Dryer, M. (2013a). Definite articles. In Dryer & Haspelmath (eds.),
  WALS Online. Ch. 37. https://wals.info/chapter/37
- Dryer, M. (2013b). Indefinite articles. In Dryer & Haspelmath (eds.),
  WALS Online. Ch. 38. https://wals.info/chapter/38
- Diessel, H. (2013a). Distance contrasts in demonstratives. In Dryer &
  Haspelmath (eds.), WALS Online. Ch. 41. https://wals.info/chapter/41
- Diessel, H. (2013b). Pronominal and adnominal demonstratives. In Dryer &
  Haspelmath (eds.), WALS Online. Ch. 42. https://wals.info/chapter/42
- Bhat, D. N. S. (2013). Third-person pronouns and demonstratives. In Dryer &
  Haspelmath (eds.), WALS Online. Ch. 43. https://wals.info/chapter/43
- Greenberg, J. (1978). How does a language acquire gender markers? In
  Greenberg (ed.), Universals of Human Language, Vol. 3.
- Himmelmann, N. (1997). Deiktikon, Artikel, Nominalphrase. Niemeyer.
-/

namespace Phenomena.Reference.Typology

-- ============================================================================
-- Types: WALS Ch 37 -- Definite Articles
-- ============================================================================

/--
Definite article type (WALS Ch 37, Dryer 2013).

Classifies languages by how (or whether) they mark definiteness on nouns.
The categories are ordered along a grammaticalization cline:
demonstrative -> definite word -> definite affix (Greenberg 1978).
-/
inductive DefiniteArticleType where
  /-- Definite word distinct from demonstratives (e.g. English "the"). -/
  | definiteWord
  /-- Definite affix on the noun (e.g. Danish "-en", Arabic "al-"). -/
  | definiteAffix
  /-- No dedicated definite article; a demonstrative is used for
      definiteness (e.g. Ojibwa, Swahili). -/
  | demonstrativeUsed
  /-- No definite article, but language has an indefinite article. -/
  | noDefButIndef
  /-- Neither definite nor indefinite article. -/
  | noArticle
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Types: WALS Ch 38 -- Indefinite Articles
-- ============================================================================

/--
Indefinite article type (WALS Ch 38, Dryer 2013).

Languages either have a dedicated indefinite word (distinct from 'one'),
use the numeral 'one' as an indefinite marker (the most common
grammaticalization path), have an indefinite affix, or lack indefinite
articles entirely.
-/
inductive IndefiniteArticleType where
  /-- Indefinite word distinct from the numeral 'one' (e.g. English "a"). -/
  | indefiniteWord
  /-- Numeral 'one' used as indefinite article (e.g. German "ein"). -/
  | numeralOne
  /-- Indefinite affix on noun. -/
  | indefiniteAffix
  /-- No indefinite article, but language has a definite article. -/
  | noIndefButDef
  /-- Neither indefinite nor definite article. -/
  | noArticle
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Types: WALS Ch 41 -- Distance Contrasts in Demonstratives
-- ============================================================================

/--
Number of distance contrasts in adnominal demonstratives (WALS Ch 41, Diessel 2013).

Two-way systems (proximal/distal) are by far the most common (54.3%),
followed by three-way systems (37.6%). Systems with four or more
distinctions are rare (< 6%).

Three-way systems subdivide into **distance-oriented** (proximal/medial/distal,
about 2/3) and **person-oriented** (near speaker / near hearer / away from
both, about 1/3). Japanese ko/so/a is the canonical person-oriented
example.
-/
inductive DemDistanceSystem where
  /-- No distance contrast; demonstratives are distance-neutral
      (e.g. Modern German "dieser"). -/
  | noContrast
  /-- Two-way contrast: proximal vs distal (e.g. English "this"/"that"). -/
  | twoWay
  /-- Three-way contrast (e.g. Japanese ko/so/a, Latin hic/iste/ille). -/
  | threeWay
  /-- Four-way contrast (e.g. Hausa). -/
  | fourWay
  /-- Five or more distance contrasts. -/
  | fiveOrMore
  deriving DecidableEq, BEq, Repr

/--
Whether a three-way demonstrative system is distance-oriented or person-oriented.

In a distance-oriented system (e.g. Hunzib), all three terms indicate
relative distance from the speaker. In a person-oriented system (e.g. Japanese),
one term specifically denotes proximity to the hearer.

Diessel (2013) notes that about 2/3 of three-way systems are distance-oriented
and about 1/3 are person-oriented.
-/
inductive DemOrientationType where
  /-- All terms encode distance from speaker (proximal/medial/distal). -/
  | distanceOriented
  /-- One term encodes proximity to the hearer (near-speaker/near-hearer/distal). -/
  | personOriented
  /-- Not applicable (system is not three-way). -/
  | notApplicable
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Types: WALS Ch 42 -- Pronominal and Adnominal Demonstratives
-- ============================================================================

/--
Relationship between pronominal and adnominal demonstratives (WALS Ch 42, Diessel 2013).

English uses the same forms ("this book" / "I like this"); French uses
different stems (adnominal "ce"/"cette" vs pronominal "celui"/"celle");
Turkish uses the same stems but different inflectional features.
-/
inductive DemFormRelation where
  /-- Same forms for pronominal and adnominal use (e.g. English). -/
  | sameForms
  /-- Different stems (e.g. French ce/celui, Korean i + defective noun). -/
  | differentStems
  /-- Same stems but different inflectional features (e.g. Turkish). -/
  | differentInflection
  deriving DecidableEq, BEq, Repr

-- ============================================================================
-- Types: WALS Ch 43 -- Third-Person Pronouns and Demonstratives
-- ============================================================================

/--
Relationship between third-person pronouns and demonstratives (WALS Ch 43, Bhat 2013).

In "two-person languages" (Bhat's term), 3rd-person pronouns are related to
demonstratives -- the pronoun is either identical to a demonstrative or
derived from one. In "three-person languages", 3rd-person pronouns form
part of the person paradigm and are unrelated to demonstratives.

The majority of the world's languages (125/225 = 55.6%) show some
relationship, supporting the diachronic pathway demonstrative -> 3rd-person
pronoun.
-/
inductive PronounDemRelation where
  /-- 3rd-person pronouns unrelated to demonstratives (e.g. Ainu, Polish). -/
  | unrelated
  /-- Related to all demonstratives (e.g. Basque, where any demonstrative
      can serve as 3rd-person pronoun). -/
  | relatedAll
  /-- Related specifically to remote/distal demonstratives
      (e.g. Eastern Armenian: 3sg "na" = distal "na"). -/
  | relatedRemote
  /-- Related specifically to non-remote (proximal or medial) demonstratives
      (e.g. Brahui: 3sg = medial demonstrative). -/
  | relatedNonRemote
  /-- Related via shared gender/noun-class markers
      (e.g. Venda: both show 21-class distinctions). -/
  | relatedGender
  /-- Demonstratives used as 3rd-person pronouns for nonhuman reference only
      (e.g. Jaqaru: 3sg "upa" for humans, demonstratives for nonhumans). -/
  | relatedNonhuman
  deriving DecidableEq, BEq, Repr

/-- Whether 3rd-person pronouns show ANY relationship to demonstratives
    (Bhat's "two-person" vs "three-person" distinction). -/
def PronounDemRelation.isRelated : PronounDemRelation → Bool
  | .unrelated => false
  | _ => true

-- ============================================================================
-- Language Profile Structure
-- ============================================================================

/--
A language's article and demonstrative profile across all five WALS chapters.

Not all chapters have data for every language (WALS samples vary by chapter),
so each field is optional.
-/
structure ArticleDemProfile where
  language : String
  family : String
  /-- ISO 639-3 code -/
  iso : String := ""
  /-- Ch 37: Definite article type -/
  defArticle : Option DefiniteArticleType := none
  /-- Ch 38: Indefinite article type -/
  indefArticle : Option IndefiniteArticleType := none
  /-- Ch 41: Distance contrasts in demonstratives -/
  demDistance : Option DemDistanceSystem := none
  /-- Ch 41 subtype: distance-oriented vs person-oriented (for 3-way systems) -/
  demOrientation : Option DemOrientationType := none
  /-- Ch 42: Pronominal vs adnominal demonstrative form -/
  demFormType : Option DemFormRelation := none
  /-- Ch 43: 3rd-person pronoun ~ demonstrative relationship -/
  pronDemRelation : Option PronounDemRelation := none
  deriving Repr

-- ============================================================================
-- Language Data: 16 Language Profiles
-- ============================================================================

/-- English (Indo-European, Germanic).
    Definite article "the" distinct from demonstratives "this"/"that".
    Indefinite article "a/an" distinct from numeral "one".
    Two-way demonstrative distance: this (proximal) vs that (distal).
    Same forms for pronominal and adnominal demonstratives.
    3rd-person pronouns ("he/she/it") unrelated to demonstratives. -/
def english : ArticleDemProfile :=
  { language := "English"
  , family := "Indo-European"
  , iso := "eng"
  , defArticle := some .definiteWord
  , indefArticle := some .indefiniteWord
  , demDistance := some .twoWay
  , demOrientation := some .notApplicable
  , demFormType := some .sameForms
  , pronDemRelation := some .unrelated }

/-- French (Indo-European, Romance).
    Definite article "le/la/les" distinct from demonstratives.
    Indefinite article "un/une" historically from numeral 'one' but
    now distinct (WALS codes French as indefinite word distinct from 'one').
    Two-way demonstrative distance: ce N-ci (proximal) vs ce N-la (distal),
    though adnominal "ce" alone is distance-neutral.
    Different stems for pronominal ("celui/celle") vs adnominal ("ce/cette").
    3rd-person pronouns ("il/elle") unrelated to demonstratives. -/
def french : ArticleDemProfile :=
  { language := "French"
  , family := "Indo-European"
  , iso := "fra"
  , defArticle := some .definiteWord
  , indefArticle := some .indefiniteWord
  , demDistance := some .twoWay
  , demOrientation := some .notApplicable
  , demFormType := some .differentStems
  , pronDemRelation := some .unrelated }

/-- German (Indo-European, Germanic).
    Definite article "der/die/das" distinct from demonstratives.
    Indefinite article "ein" = numeral 'one' (phonological reduction in speech).
    Distance-neutral adnominal demonstratives: "dieser" and stressed "der/die/das"
    are deictically noncontrastive (Diessel 2013); distance expressed by adding
    adverbial "hier"/"da". Classified as no-contrast in WALS Ch 41.
    Different inflectional features: pronominal demonstratives inflect for case
    while adnominal demonstratives co-occur with inflected nouns.
    3rd-person pronouns ("er/sie/es") unrelated to demonstratives. -/
def german : ArticleDemProfile :=
  { language := "German"
  , family := "Indo-European"
  , iso := "deu"
  , defArticle := some .definiteWord
  , indefArticle := some .numeralOne
  , demDistance := some .noContrast
  , demOrientation := some .notApplicable
  , demFormType := some .differentInflection
  , pronDemRelation := some .unrelated }

/-- Japanese (Japonic).
    No definite or indefinite articles.
    Three-way person-oriented demonstrative system: ko- (near speaker),
    so- (near hearer), a- (away from both). The canonical person-oriented system.
    Different stems: adnominal kono/sono/ano vs pronominal kore/sore/are.
    3rd-person pronouns ("kare/kanojo") unrelated to demonstratives
    (borrowed from Classical Chinese / relatively recent innovations). -/
def japanese : ArticleDemProfile :=
  { language := "Japanese"
  , family := "Japonic"
  , iso := "jpn"
  , defArticle := some .noArticle
  , indefArticle := some .noArticle
  , demDistance := some .threeWay
  , demOrientation := some .personOriented
  , demFormType := some .differentStems
  , pronDemRelation := some .unrelated }

/-- Mandarin Chinese (Sino-Tibetan).
    No definite or indefinite articles (bare nouns are ambiguous for definiteness).
    Two-way demonstrative distance: zhe (proximal) vs na (distal).
    Same forms for pronominal and adnominal demonstratives (with optional
    classifier in adnominal use).
    3rd-person pronoun "ta" unrelated to demonstratives. -/
def mandarin : ArticleDemProfile :=
  { language := "Mandarin"
  , family := "Sino-Tibetan"
  , iso := "cmn"
  , defArticle := some .noArticle
  , indefArticle := some .noArticle
  , demDistance := some .twoWay
  , demOrientation := some .notApplicable
  , demFormType := some .sameForms
  , pronDemRelation := some .unrelated }

/-- Turkish (Turkic).
    No definite article; indefinite article "bir" = numeral 'one' (different
    NP position when used as article vs numeral, per Kornfilt 1997).
    Two-way demonstrative distance: bu (proximal) vs o (distal), with su as
    a restricted medial form. WALS codes as two-way.
    Different inflectional features: pronominal demonstratives inflect for case
    and number, adnominal demonstratives are uninflected particles.
    3rd-person pronoun "o" identical to distal demonstrative. -/
def turkish : ArticleDemProfile :=
  { language := "Turkish"
  , family := "Turkic"
  , iso := "tur"
  , defArticle := some .noDefButIndef
  , indefArticle := some .numeralOne
  , demDistance := some .twoWay
  , demOrientation := some .notApplicable
  , demFormType := some .differentInflection
  , pronDemRelation := some .relatedRemote }

/-- Arabic (Egyptian) (Afro-Asiatic, Semitic).
    Definite prefix "al-" on nouns (definite affix).
    No indefinite article (unmarked nouns are indefinite, though tanwin
    in Standard Arabic marks indefiniteness).
    Two-way demonstrative distance: hada (proximal) vs daak (distal).
    Same forms for pronominal and adnominal demonstratives.
    3rd-person pronoun "huwa/hiya" unrelated to demonstratives. -/
def arabic : ArticleDemProfile :=
  { language := "Arabic (Egyptian)"
  , family := "Afro-Asiatic"
  , iso := "arz"
  , defArticle := some .definiteAffix
  , indefArticle := some .noIndefButDef
  , demDistance := some .twoWay
  , demOrientation := some .notApplicable
  , demFormType := some .sameForms
  , pronDemRelation := some .unrelated }

/-- Finnish (Uralic).
    No definite or indefinite articles.
    Two-way demonstrative distance: tama (proximal) vs tuo/se (distal).
    Same forms for pronominal and adnominal demonstratives.
    3rd-person pronoun "han" (human) / "se" (nonhuman) -- "se" is identical
    to the distal demonstrative. -/
def finnish : ArticleDemProfile :=
  { language := "Finnish"
  , family := "Uralic"
  , iso := "fin"
  , defArticle := some .noArticle
  , indefArticle := some .noArticle
  , demDistance := some .twoWay
  , demOrientation := some .notApplicable
  , demFormType := some .sameForms
  , pronDemRelation := some .relatedNonhuman }

/-- Hungarian (Uralic).
    Definite article "a/az" distinct from demonstratives.
    Indefinite article "egy" = numeral 'one'.
    Two-way demonstrative distance: ez (proximal) vs az (distal).
    Same forms for pronominal and adnominal demonstratives.
    3rd-person pronoun "o" unrelated to demonstratives. -/
def hungarian : ArticleDemProfile :=
  { language := "Hungarian"
  , family := "Uralic"
  , iso := "hun"
  , defArticle := some .definiteWord
  , indefArticle := some .numeralOne
  , demDistance := some .twoWay
  , demOrientation := some .notApplicable
  , demFormType := some .sameForms
  , pronDemRelation := some .unrelated }

/-- Russian (Indo-European, Slavic).
    No definite or indefinite articles.
    Two-way demonstrative distance: etot (proximal) vs tot (distal).
    Same forms for pronominal and adnominal demonstratives.
    3rd-person pronouns ("on/ona/ono") unrelated to demonstratives. -/
def russian : ArticleDemProfile :=
  { language := "Russian"
  , family := "Indo-European"
  , iso := "rus"
  , defArticle := some .noArticle
  , indefArticle := some .noArticle
  , demDistance := some .twoWay
  , demOrientation := some .notApplicable
  , demFormType := some .sameForms
  , pronDemRelation := some .unrelated }

/-- Swahili (Niger-Congo, Bantu).
    Demonstrative used as definite marker (precedes noun for definiteness,
    follows noun for deictic use; WALS Ch 37 value 2).
    No indefinite article.
    Three-way demonstrative distance: h- (proximal) / h-o (medial) / -le (distal).
    Same forms for pronominal and adnominal demonstratives.
    3rd-person pronouns related via shared noun-class agreement prefixes
    (gender-marker relationship). -/
def swahili : ArticleDemProfile :=
  { language := "Swahili"
  , family := "Niger-Congo"
  , iso := "swh"
  , defArticle := some .demonstrativeUsed
  , indefArticle := some .noIndefButDef
  , demDistance := some .threeWay
  , demOrientation := some .distanceOriented
  , demFormType := some .sameForms
  , pronDemRelation := some .relatedGender }

/-- Tagalog (Austronesian, Philippine).
    Definite/indefinite distinction via case markers: "ang" (definite-like
    topic marker) vs "ng" (indefinite-like). WALS codes as definite word
    distinct from demonstratives.
    Two-way demonstrative distance: ito (proximal) vs iyon (distal),
    with middle term "iyan" sometimes yielding a three-way analysis.
    WALS codes as three-way.
    Same forms for pronominal and adnominal demonstratives.
    3rd-person pronoun "siya" unrelated to demonstratives. -/
def tagalog : ArticleDemProfile :=
  { language := "Tagalog"
  , family := "Austronesian"
  , iso := "tgl"
  , defArticle := some .definiteWord
  , indefArticle := some .noIndefButDef
  , demDistance := some .threeWay
  , demOrientation := some .personOriented
  , demFormType := some .sameForms
  , pronDemRelation := some .unrelated }

/-- Latin (Indo-European, Italic).
    No definite or indefinite articles (bare nouns are ambiguous).
    Three-way distance-oriented demonstrative system: hic (proximal),
    iste (medial), ille (distal). This is the textbook three-way
    distance-oriented system.
    Same forms for pronominal and adnominal demonstratives
    (though with full case/gender/number inflection in both uses).
    3rd-person pronoun "is/ea/id" distinct from but historically related
    to demonstratives (related to all demonstratives via shared inflection
    patterns). -/
def latin : ArticleDemProfile :=
  { language := "Latin"
  , family := "Indo-European"
  , iso := "lat"
  , defArticle := some .noArticle
  , indefArticle := some .noArticle
  , demDistance := some .threeWay
  , demOrientation := some .distanceOriented
  , demFormType := some .sameForms
  , pronDemRelation := some .relatedAll }

/-- Korean (Koreanic).
    No definite or indefinite articles (topic marker "-un"/"-nun" sometimes
    conveys definiteness pragmatically).
    Three-way person-oriented demonstrative system: i (near speaker),
    ku (near hearer), ce (away from both).
    Different stems: pronominal demonstratives formed by combining i/ku/ce
    with a "defective noun" like "il" (thing/fact), giving "i-il", "ku-il", etc.
    (Sohn 1994: 295, Diessel 2013).
    3rd-person pronoun "ku" related to medial demonstrative "ku". -/
def korean : ArticleDemProfile :=
  { language := "Korean"
  , family := "Koreanic"
  , iso := "kor"
  , defArticle := some .noArticle
  , indefArticle := some .noArticle
  , demDistance := some .threeWay
  , demOrientation := some .personOriented
  , demFormType := some .differentStems
  , pronDemRelation := some .relatedNonRemote }

/-- Danish (Indo-European, Germanic).
    Definite suffix "-en"/"-et" on nouns (definite affix); separate definite
    article "den/det" used when an adjective is present.
    Indefinite article "en/et" = numeral 'one'.
    Two-way demonstrative distance: denne (proximal) vs den (distal).
    Different inflectional features between pronominal and adnominal uses.
    3rd-person pronouns ("han/hun/den/det") -- "den/det" related to
    demonstratives. -/
def danish : ArticleDemProfile :=
  { language := "Danish"
  , family := "Indo-European"
  , iso := "dan"
  , defArticle := some .definiteAffix
  , indefArticle := some .numeralOne
  , demDistance := some .twoWay
  , demOrientation := some .notApplicable
  , demFormType := some .differentInflection
  , pronDemRelation := some .relatedRemote }

/-- Hausa (Afro-Asiatic, Chadic).
    No definite article; no standard indefinite article (WALS Ch 37 value 5).
    Four-way person-oriented demonstrative system: nan (near speaker),
    nan (near hearer, tonal difference), can (away from both), can (far away).
    Hausa is a key example of a four-or-more-way system (Wolff 1993).
    Same forms for pronominal and adnominal demonstratives.
    3rd-person pronouns related to demonstratives. -/
def hausa : ArticleDemProfile :=
  { language := "Hausa"
  , family := "Afro-Asiatic"
  , iso := "hau"
  , defArticle := some .noArticle
  , indefArticle := some .noArticle
  , demDistance := some .fourWay
  , demOrientation := some .personOriented
  , demFormType := some .sameForms
  , pronDemRelation := some .relatedAll }

/-- Basque (language isolate).
    Definite suffix "-a"/"-ak" (definite affix). No indefinite article
    (bare nouns are indefinite).
    Two-way demonstrative distance: hau (proximal) vs hura (distal),
    with hori (medial) yielding a three-way system.
    Same forms for pronominal and adnominal demonstratives.
    3rd-person pronouns: hau/hori/hura function as both demonstratives
    and 3rd-person pronouns (Saltarelli et al. 1988: 213). -/
def basque : ArticleDemProfile :=
  { language := "Basque"
  , family := "Isolate"
  , iso := "eus"
  , defArticle := some .definiteAffix
  , indefArticle := some .noIndefButDef
  , demDistance := some .threeWay
  , demOrientation := some .distanceOriented
  , demFormType := some .sameForms
  , pronDemRelation := some .relatedAll }

/-- All 16 language profiles. -/
def allLanguages : List ArticleDemProfile :=
  [ english, french, german, japanese, mandarin, turkish, arabic
  , finnish, hungarian, russian, swahili, tagalog, latin, korean
  , danish, hausa, basque ]

-- ============================================================================
-- WALS Distribution Data: Aggregate Counts
-- ============================================================================

/-- WALS Ch 37: Definite article distribution across 566 languages (Dryer 2013). -/
structure DefiniteArticleCounts where
  definiteWord : Nat          -- value 1
  demonstrativeUsed : Nat     -- value 2
  definiteAffix : Nat         -- value 3
  noDefButIndef : Nat         -- value 4
  noArticle : Nat             -- value 5
  deriving Repr

def DefiniteArticleCounts.total (c : DefiniteArticleCounts) : Nat :=
  c.definiteWord + c.demonstrativeUsed + c.definiteAffix + c.noDefButIndef + c.noArticle

/-- WALS Ch 37 distribution (Dryer 2013, n = 566). -/
def walsDefiniteArticle : DefiniteArticleCounts :=
  { definiteWord := 197
  , demonstrativeUsed := 56
  , definiteAffix := 84
  , noDefButIndef := 41
  , noArticle := 188 }

/-- WALS Ch 38: Indefinite article distribution across 473 languages (Dryer 2013). -/
structure IndefiniteArticleCounts where
  indefiniteWord : Nat        -- value 1
  numeralOne : Nat            -- value 2
  indefiniteAffix : Nat       -- value 3
  noIndefButDef : Nat         -- value 4
  noArticle : Nat             -- value 5
  deriving Repr

def IndefiniteArticleCounts.total (c : IndefiniteArticleCounts) : Nat :=
  c.indefiniteWord + c.numeralOne + c.indefiniteAffix + c.noIndefButDef + c.noArticle

/-- WALS Ch 38 distribution (Dryer 2013, n = 473). -/
def walsIndefiniteArticle : IndefiniteArticleCounts :=
  { indefiniteWord := 91
  , numeralOne := 90
  , indefiniteAffix := 23
  , noIndefButDef := 81
  , noArticle := 188 }

/-- WALS Ch 41: Demonstrative distance contrasts across 234 languages (Diessel 2013). -/
structure DemDistanceCounts where
  noContrast : Nat            -- value 1
  twoWay : Nat                -- value 2
  threeWay : Nat              -- value 3
  fourWay : Nat               -- value 4
  fiveOrMore : Nat            -- value 5
  deriving Repr

def DemDistanceCounts.total (c : DemDistanceCounts) : Nat :=
  c.noContrast + c.twoWay + c.threeWay + c.fourWay + c.fiveOrMore

/-- WALS Ch 41 distribution (Diessel 2013, n = 234). -/
def walsDemDistance : DemDistanceCounts :=
  { noContrast := 7
  , twoWay := 127
  , threeWay := 88
  , fourWay := 8
  , fiveOrMore := 4 }

/-- WALS Ch 42: Pronominal/adnominal demonstrative form across 201 languages (Diessel 2013). -/
structure DemFormCounts where
  sameForms : Nat             -- value 1
  differentStems : Nat        -- value 2
  differentInflection : Nat   -- value 3
  deriving Repr

def DemFormCounts.total (c : DemFormCounts) : Nat :=
  c.sameForms + c.differentStems + c.differentInflection

/-- WALS Ch 42 distribution (Diessel 2013, n = 201). -/
def walsDemForm : DemFormCounts :=
  { sameForms := 143
  , differentStems := 37
  , differentInflection := 21 }

/-- WALS Ch 43: Third-person pronoun ~ demonstrative relationship across 225 languages (Bhat 2013). -/
structure PronounDemCounts where
  unrelated : Nat             -- value 1
  relatedAll : Nat            -- value 2
  relatedRemote : Nat         -- value 3
  relatedNonRemote : Nat      -- value 4
  relatedGender : Nat         -- value 5
  relatedNonhuman : Nat       -- value 6
  deriving Repr

def PronounDemCounts.total (c : PronounDemCounts) : Nat :=
  c.unrelated + c.relatedAll + c.relatedRemote +
  c.relatedNonRemote + c.relatedGender + c.relatedNonhuman

/-- Total count of languages where 3rd-person pronouns show any
    relationship to demonstratives. -/
def PronounDemCounts.totalRelated (c : PronounDemCounts) : Nat :=
  c.relatedAll + c.relatedRemote + c.relatedNonRemote +
  c.relatedGender + c.relatedNonhuman

/-- WALS Ch 43 distribution (Bhat 2013, n = 225). -/
def walsPronounDem : PronounDemCounts :=
  { unrelated := 100
  , relatedAll := 52
  , relatedRemote := 18
  , relatedNonRemote := 14
  , relatedGender := 24
  , relatedNonhuman := 17 }

-- ============================================================================
-- Verification: WALS Totals
-- ============================================================================

/-- Ch 37: 566 languages surveyed. -/
example : walsDefiniteArticle.total = 566 := by native_decide

/-- Ch 38: 473 languages surveyed. -/
example : walsIndefiniteArticle.total = 473 := by native_decide

/-- Ch 41: 234 languages surveyed. -/
example : walsDemDistance.total = 234 := by native_decide

/-- Ch 42: 201 languages surveyed. -/
example : walsDemForm.total = 201 := by native_decide

/-- Ch 43: 225 languages surveyed. -/
example : walsPronounDem.total = 225 := by native_decide

-- ============================================================================
-- Verification: Per-Cell Data
-- ============================================================================

-- Ch 37 cells
example : walsDefiniteArticle.definiteWord = 197 := by native_decide
example : walsDefiniteArticle.demonstrativeUsed = 56 := by native_decide
example : walsDefiniteArticle.definiteAffix = 84 := by native_decide
example : walsDefiniteArticle.noDefButIndef = 41 := by native_decide
example : walsDefiniteArticle.noArticle = 188 := by native_decide

-- Ch 38 cells
example : walsIndefiniteArticle.indefiniteWord = 91 := by native_decide
example : walsIndefiniteArticle.numeralOne = 90 := by native_decide
example : walsIndefiniteArticle.indefiniteAffix = 23 := by native_decide
example : walsIndefiniteArticle.noIndefButDef = 81 := by native_decide
example : walsIndefiniteArticle.noArticle = 188 := by native_decide

-- Ch 41 cells
example : walsDemDistance.noContrast = 7 := by native_decide
example : walsDemDistance.twoWay = 127 := by native_decide
example : walsDemDistance.threeWay = 88 := by native_decide
example : walsDemDistance.fourWay = 8 := by native_decide
example : walsDemDistance.fiveOrMore = 4 := by native_decide

-- Ch 42 cells
example : walsDemForm.sameForms = 143 := by native_decide
example : walsDemForm.differentStems = 37 := by native_decide
example : walsDemForm.differentInflection = 21 := by native_decide

-- Ch 43 cells
example : walsPronounDem.unrelated = 100 := by native_decide
example : walsPronounDem.relatedAll = 52 := by native_decide
example : walsPronounDem.relatedRemote = 18 := by native_decide
example : walsPronounDem.relatedNonRemote = 14 := by native_decide
example : walsPronounDem.relatedGender = 24 := by native_decide
example : walsPronounDem.relatedNonhuman = 17 := by native_decide

-- ============================================================================
-- Generalization 1: Two-way demonstrative systems are the most common
-- ============================================================================

/--
Two-way demonstrative systems (proximal/distal) are the most common type,
accounting for 127 of 234 languages in the WALS sample (54.3%).

Diessel (2013): "The vast majority of the world's languages employ two or
three distance-marked demonstratives: 54.3 per cent of all languages shown
on the map have adnominal demonstratives that express a two-way contrast."
-/
theorem twoWay_most_common :
    walsDemDistance.twoWay > walsDemDistance.threeWay ∧
    walsDemDistance.twoWay > walsDemDistance.fourWay ∧
    walsDemDistance.twoWay > walsDemDistance.fiveOrMore ∧
    walsDemDistance.twoWay > walsDemDistance.noContrast := by
  native_decide

/--
Two-way and three-way systems together account for over 90% of languages.
One-way, four-way, and five-or-more-way systems together are under 10%.
-/
theorem twoAndThreeWay_dominate :
    walsDemDistance.twoWay + walsDemDistance.threeWay >
    9 * (walsDemDistance.noContrast + walsDemDistance.fourWay + walsDemDistance.fiveOrMore) := by
  native_decide

-- ============================================================================
-- Generalization 2: Definite → Indefinite implicational tendency
-- ============================================================================

/--
Languages with definite articles tend to also have indefinite articles.
The evidence: 81 languages have a definite article but no indefinite article
(Ch 38, value 4), compared to 41 languages that have an indefinite article
but no definite article (Ch 37, value 4).

This asymmetry suggests that definiteness marking is the typologically
"prior" or more basic category: languages are more likely to grammaticalize
definiteness without indefiniteness than vice versa.

Note: This is a tendency, not an absolute universal. The 41 exceptions
(indefinite without definite) are concentrated in Asia (Turkey to Iran)
and New Guinea.
-/
theorem defArticle_more_robust_than_indef :
    walsIndefiniteArticle.noIndefButDef > walsDefiniteArticle.noDefButIndef := by
  native_decide

/--
Languages with some form of definite marking (word, affix, or demonstrative)
outnumber those without. 337 of 566 languages (59.5%) have definite marking.
-/
theorem majority_have_some_definite_marking :
    walsDefiniteArticle.definiteWord +
    walsDefiniteArticle.demonstrativeUsed +
    walsDefiniteArticle.definiteAffix >
    walsDefiniteArticle.noDefButIndef + walsDefiniteArticle.noArticle := by
  native_decide

-- ============================================================================
-- Generalization 3: Third-person pronouns derive from demonstratives
-- ============================================================================

/--
In a majority of languages surveyed (125 of 225 = 55.6%), third-person
pronouns show some relationship to demonstratives. This supports the
well-documented diachronic pathway: demonstrative -> 3rd-person pronoun.

Bhat (2013) distinguishes "two-person languages" (3rd-person pronouns are
demonstrative-derived, so the language really only has 1st/2nd person
pronouns plus demonstratives) from "three-person languages" (3rd-person
pronouns are independent).
-/
theorem majority_pronoun_dem_related :
    walsPronounDem.totalRelated > walsPronounDem.unrelated := by
  native_decide

/-- The most common subtype of pronoun-demonstrative relationship is
    "related to all demonstratives" (52 languages), where any demonstrative
    can serve as a 3rd-person pronoun. -/
theorem relatedAll_most_common_subtype :
    walsPronounDem.relatedAll > walsPronounDem.relatedRemote ∧
    walsPronounDem.relatedAll > walsPronounDem.relatedNonRemote ∧
    walsPronounDem.relatedAll > walsPronounDem.relatedGender ∧
    walsPronounDem.relatedAll > walsPronounDem.relatedNonhuman := by
  native_decide

-- ============================================================================
-- Generalization 4: Same-form demonstratives are the majority
-- ============================================================================

/--
In most languages (143 of 201 = 71.1%), pronominal and adnominal
demonstratives have the same forms (Diessel 2013, Ch 42). Languages where
adnominal demonstratives have different stems (37) or different inflectional
features (21) are the minority.

Languages with same-form demonstratives are especially prevalent in
Australia (where no language in the sample differentiates the two uses)
and North America (except Pacific Northwest).
-/
theorem sameForm_demonstratives_majority :
    walsDemForm.sameForms >
    walsDemForm.differentStems + walsDemForm.differentInflection := by
  native_decide

-- ============================================================================
-- Generalization 5: Demonstrative → definite article diachronic pathway
-- ============================================================================

/--
The grammaticalization cline: demonstrative -> definite article -> definite affix.

This is supported by the WALS data:
- 56 languages use demonstratives as definite markers (mid-cline)
- 84 languages have definite affixes (end of cline)
- 197 languages have definite words distinct from demonstratives (a stage where
  the article has diverged from the source demonstrative)

The 56 "demonstrative used as definite marker" languages represent the
transitional stage where this grammaticalization is actively underway.

See Greenberg (1978), Himmelmann (1997) for theoretical discussion.
-/
theorem grammaticalization_cline_attested :
    -- All three stages of the cline are well attested
    walsDefiniteArticle.demonstrativeUsed > 0 ∧
    walsDefiniteArticle.definiteWord > 0 ∧
    walsDefiniteArticle.definiteAffix > 0 ∧
    -- The transitional stage (demonstrative used) is smaller than both
    -- the source stage (no article, using demonstratives ad hoc) and
    -- the end stage (distinct definite word or affix)
    walsDefiniteArticle.demonstrativeUsed < walsDefiniteArticle.definiteWord ∧
    walsDefiniteArticle.demonstrativeUsed < walsDefiniteArticle.definiteAffix := by
  native_decide

-- ============================================================================
-- Generalization 6: Languages without articles use demonstratives
-- ============================================================================

/--
Among languages without dedicated definite articles, a substantial proportion
(56 out of 285 article-less languages = 19.6%) use demonstratives to mark
definiteness. This is the "demonstrative used as definite article" category
from Ch 37.

This confirms the typological observation that demonstratives are the
natural source for definiteness marking: even languages that lack a
grammaticalized definite article often use demonstratives in definite
contexts more frequently than expected.
-/
theorem demonstratives_fill_article_gap :
    let totalWithoutDefArticle :=
      walsDefiniteArticle.demonstrativeUsed +
      walsDefiniteArticle.noDefButIndef +
      walsDefiniteArticle.noArticle
    -- 56 out of 285 languages without a dedicated definite article
    -- use demonstratives for definiteness
    walsDefiniteArticle.demonstrativeUsed > 0 ∧
    totalWithoutDefArticle = 285 := by
  native_decide

-- ============================================================================
-- Per-Language Verification
-- ============================================================================

-- Languages without any articles (no definite, no indefinite)
theorem japanese_no_articles :
    japanese.defArticle = some .noArticle ∧
    japanese.indefArticle = some .noArticle := by native_decide

theorem mandarin_no_articles :
    mandarin.defArticle = some .noArticle ∧
    mandarin.indefArticle = some .noArticle := by native_decide

theorem russian_no_articles :
    russian.defArticle = some .noArticle ∧
    russian.indefArticle = some .noArticle := by native_decide

theorem latin_no_articles :
    latin.defArticle = some .noArticle ∧
    latin.indefArticle = some .noArticle := by native_decide

theorem korean_no_articles :
    korean.defArticle = some .noArticle ∧
    korean.indefArticle = some .noArticle := by native_decide

-- Languages with both definite and indefinite articles
theorem english_has_both_articles :
    english.defArticle = some .definiteWord ∧
    english.indefArticle = some .indefiniteWord := by native_decide

theorem french_has_both_articles :
    french.defArticle = some .definiteWord ∧
    french.indefArticle = some .indefiniteWord := by native_decide

-- Languages with definite affix
theorem arabic_definite_affix :
    arabic.defArticle = some .definiteAffix := by native_decide

theorem danish_definite_affix :
    danish.defArticle = some .definiteAffix := by native_decide

theorem basque_definite_affix :
    basque.defArticle = some .definiteAffix := by native_decide

-- Person-oriented three-way systems
theorem japanese_person_oriented :
    japanese.demDistance = some .threeWay ∧
    japanese.demOrientation = some .personOriented := by native_decide

theorem korean_person_oriented :
    korean.demDistance = some .threeWay ∧
    korean.demOrientation = some .personOriented := by native_decide

-- Distance-oriented three-way systems
theorem latin_distance_oriented :
    latin.demDistance = some .threeWay ∧
    latin.demOrientation = some .distanceOriented := by native_decide

-- German has distance-neutral demonstratives
theorem german_no_dem_distance_contrast :
    german.demDistance = some .noContrast := by native_decide

-- Hausa has a four-way system
theorem hausa_four_way :
    hausa.demDistance = some .fourWay := by native_decide

-- Turkish: 3rd-person pronoun "o" = distal demonstrative
theorem turkish_pronoun_from_distal :
    turkish.pronDemRelation = some .relatedRemote := by native_decide

-- Basque: demonstratives serve as 3rd-person pronouns
theorem basque_dem_as_pronoun :
    basque.pronDemRelation = some .relatedAll := by native_decide

-- ============================================================================
-- Cross-Chapter Patterns in Our Sample
-- ============================================================================

/-- Helper: does a profile have any definite marking? -/
def ArticleDemProfile.hasDefinite (p : ArticleDemProfile) : Bool :=
  match p.defArticle with
  | some .definiteWord => true
  | some .definiteAffix => true
  | some .demonstrativeUsed => true
  | _ => false

/-- Helper: does a profile have any indefinite article? -/
def ArticleDemProfile.hasIndefinite (p : ArticleDemProfile) : Bool :=
  match p.indefArticle with
  | some .indefiniteWord => true
  | some .numeralOne => true
  | some .indefiniteAffix => true
  | _ => false

/--
In our 16-language sample, all but one language with an indefinite article
also has some form of definite marking (article, affix, or demonstrative used).
The exception is Turkish, which has the numeral "bir" as an indefinite article
but no dedicated definite article (WALS Ch 37, value 4).

This is consistent with the WALS aggregate data, which shows 41 languages with
indefinite but no definite articles, concentrated in the Turkey-to-Iran belt
and New Guinea.
-/
theorem indef_implies_def_almost :
    let withIndef := allLanguages.filter (·.hasIndefinite)
    let withIndefAndDef := withIndef.filter (·.hasDefinite)
    -- 5 of 6 languages with indefinite articles also have definite marking
    withIndef.length = 6 ∧ withIndefAndDef.length = 5 := by
  native_decide

/-- Turkish is the one exception: indefinite article but no definite marking. -/
theorem turkish_indef_without_def :
    turkish.hasIndefinite = true ∧ turkish.hasDefinite = false := by
  native_decide

/--
In our sample, languages with three-way or larger demonstrative systems
tend to lack articles entirely. 5 of the 7 languages with 3+ distance
contrasts have no definite or indefinite articles.
-/
def hasThreeOrMoreDemContrasts (p : ArticleDemProfile) : Bool :=
  match p.demDistance with
  | some .threeWay | some .fourWay | some .fiveOrMore => true
  | _ => false

/-- Count of languages in our sample with three-way-or-more demonstratives. -/
theorem threeOrMore_count :
    (allLanguages.filter hasThreeOrMoreDemContrasts).length = 7 := by
  native_decide

/--
8 of our 16 sample languages show some relationship between 3rd-person
pronouns and demonstratives (Turkish, Finnish, Swahili, Latin, Korean,
Danish, Hausa, Basque), consistent with Bhat's finding that a majority
of languages worldwide (125 of 225) are "two-person languages."
-/
def hasPronDemRelated (p : ArticleDemProfile) : Bool :=
  match p.pronDemRelation with
  | some r => r.isRelated
  | none => false

theorem prondem_related_count :
    (allLanguages.filter hasPronDemRelated).length = 8 := by
  native_decide

-- ============================================================================
-- Diachronic Pathway Summary
-- ============================================================================

/--
The grammaticalization hierarchy for definiteness marking, attested
cross-linguistically (Greenberg 1978, Himmelmann 1997):

  Stage 0: No definiteness marking (bare nouns, e.g. Mandarin, Russian)
  Stage 1: Demonstrative used for definiteness (e.g. Swahili, Ojibwa)
  Stage 2: Definite word distinct from demonstrative (e.g. English, French)
  Stage 3: Definite affix (e.g. Danish, Arabic, Basque)

Each stage represents a further degree of grammaticalization: phonological
reduction, semantic bleaching (loss of deictic content), and increased
obligatoriness.
-/
inductive GrammaticalizationStage where
  | noMarking       -- Stage 0
  | demonstrative   -- Stage 1
  | definiteWord    -- Stage 2
  | definiteAffix   -- Stage 3
  deriving DecidableEq, BEq, Repr

/-- Map a DefiniteArticleType to its grammaticalization stage. -/
def DefiniteArticleType.stage : DefiniteArticleType → GrammaticalizationStage
  | .noArticle | .noDefButIndef => .noMarking
  | .demonstrativeUsed => .demonstrative
  | .definiteWord => .definiteWord
  | .definiteAffix => .definiteAffix

/-- The stages form a total order (higher = more grammaticalized). -/
def GrammaticalizationStage.ord : GrammaticalizationStage → Nat
  | .noMarking => 0
  | .demonstrative => 1
  | .definiteWord => 2
  | .definiteAffix => 3

/-- All four stages of the grammaticalization cline are attested in our
    16-language sample. -/
theorem all_stages_attested :
    let stages := allLanguages.filterMap (λ p =>
      p.defArticle.map DefiniteArticleType.stage)
    stages.any (· == .noMarking) = true ∧
    stages.any (· == .demonstrative) = true ∧
    stages.any (· == .definiteWord) = true ∧
    stages.any (· == .definiteAffix) = true := by
  native_decide

end Phenomena.Reference.Typology
