import Linglib.Data.Examples.Schema

/-!
# `Dolatian2020` — typed example data

Auto-generated from `Linglib/Data/Examples/Dolatian2020.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Dolatian2020.Examples`.
-/

namespace Dolatian2020.Examples

open Data.Examples

def ex_1 : LinguisticExample :=
  { id := "dolatian2020_1"
    source := ⟨"dolatian-2020", "(1)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "kórd͡z, kord͡z-avór, kord͡z-avor-nér, kord͡z-avor-nér-ə"
    discourseSegments := []
    glossedTokens := [("kórd͡z", "work"), ("kord͡z-avór", "work-er"), ("kord͡z-avor-nér", "work-er-PL"), ("kord͡z-avor-nér-ə", "work-er-PL-with")]
    translation := "work; worker; workers; with workers"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dialect", "western"), ("process", "stress")]
    comment := "Stress falls on the rightmost full vowel, whether in the root, a derivational suffix or an inflectional suffix, but never on a schwa."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_2 : LinguisticExample :=
  { id := "dolatian2020_2"
    source := ⟨"dolatian-2020", "(2)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "hín, hən-utjún; teʁín, teʁn-orág"
    discourseSegments := []
    glossedTokens := [("hín", "old"), ("hən-utjún", "old-ness"), ("teʁín", "yellow"), ("teʁn-orág", "yellow-ish")]
    translation := "old, oldness; yellow, yellowish"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "derivational"), ("reduction", "both")]
    comment := "A destressed high vowel reduces to schwa, hín ~ hən-utjún, or deletes, teʁín ~ teʁn-orág."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_3b : LinguisticExample :=
  { id := "dolatian2020_3b"
    source := ⟨"dolatian-2020", "(3b)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "had͡záχ, had͡zaχ-él; darpér, darper-él"
    discourseSegments := []
    glossedTokens := [("had͡záχ", "frequent"), ("had͡zaχ-él", "frequent-INF"), ("darpér", "different"), ("darper-él", "different-INF")]
    translation := "frequent, to frequent; different, to distinguish"
    context := ""
    judgment := .acceptable
    alternatives := [("had͡zχ-él", .ungrammatical), ("darpr-él", .ungrammatical)]
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "derivational"), ("reduction", "none")]
    comment := "Low and mid vowels do not reduce when destressed."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_4 : LinguisticExample :=
  { id := "dolatian2020_4"
    source := ⟨"dolatian-2020", "(4)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "amusín, amusn-utjún; irigún, irign-ajín"
    discourseSegments := []
    glossedTokens := [("amusín", "husband"), ("amusn-utjún", "husband-ness"), ("irigún", "evening"), ("irign-ajín", "evening-ADJ")]
    translation := "husband, marriage; evening, evening (adj.)"
    context := ""
    judgment := .acceptable
    alternatives := [("amsin-utjún", .ungrammatical), ("irgun-ajín", .ungrammatical)]
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "derivational"), ("reduction", "deletion")]
    comment := "Only the destressed high vowel reduces, the one stressed in the base and unstressed in the derivative; the other high vowels of the base stay."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_5a : LinguisticExample :=
  { id := "dolatian2020_5a"
    source := ⟨"dolatian-2020", "(5a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "d͡zín, d͡zən-únt, d͡zən-ənt-agán"
    discourseSegments := []
    glossedTokens := [("d͡zín", "birth"), ("d͡zən-únt", "birth-NMLZ"), ("d͡zən-ənt-agán", "birth-NMLZ-ADJ")]
    translation := "birth; birth; generative"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "derivational"), ("reduction", "schwa")]
    comment := "Unbounded cyclicity: reduction applies to a sequence of destressed high vowels, each new morpheme triggering a new cycle of stress shift and reduction."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_5c : LinguisticExample :=
  { id := "dolatian2020_5c"
    source := ⟨"dolatian-2020", "(5c)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "kír, kər-ít͡ʃ, dúp, kər-t͡ʃ-a-dup"
    discourseSegments := []
    glossedTokens := [("kír", "handwriting"), ("kər-ít͡ʃ", "handwriting-AGT"), ("dúp", "box"), ("kər-t͡ʃ-a-dup", "handwriting-AGT-LV-box")]
    translation := "handwriting; pen; box; pencil-box"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "compound"), ("reduction", "both")]
    comment := "Reduction applies to suffixes and in compounds: the suffix vowel of kər-ít͡ʃ is destressed and deleted in the compound."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_7a : LinguisticExample :=
  { id := "dolatian2020_7a"
    source := ⟨"dolatian-2020", "(7a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "amusín, amusn-utjún, amusin-óv"
    discourseSegments := []
    glossedTokens := [("amusín", "husband"), ("amusn-utjún", "husband-ness"), ("amusin-óv", "husband-INST")]
    translation := "husband; marriage; husband (instrumental)"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "vInflection"), ("reduction", "none")]
    comment := "In Western Armenian derivational suffixes trigger reduction and inflectional suffixes only stress shift: the stem-level against the word-level cophonology."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_7b : LinguisticExample :=
  { id := "dolatian2020_7b"
    source := ⟨"dolatian-2020", "(7b)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "zərújt͡s, zərut͡s-él, zərujt͡s-óv"
    discourseSegments := []
    glossedTokens := [("zərújt͡s", "conversation"), ("zərut͡s-él", "conversation-INF"), ("zərujt͡s-óv", "conversation-INST")]
    translation := "conversation; to converse; conversation (instrumental)"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "vInflection"), ("reduction", "diphthong")]
    comment := "The destressed diphthong uj reduces to u in derivation and not in inflection."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_10c : LinguisticExample :=
  { id := "dolatian2020_10c"
    source := ⟨"dolatian-2020", "(10c)"⟩
    reportedIn := none
    language := "nucl1235"
    primaryText := "amusn-óv"
    discourseSegments := []
    glossedTokens := [("amusn-óv", "husband-INST")]
    translation := "husband (instrumental)"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dialect", "eastern"), ("suffix", "vInflection"), ("reduction", "deletion")]
    comment := "Vowel-initial inflection triggers reduction in Eastern Armenian: the resyllabified stem-final consonant misaligns the Prosodic Stem, which expands and triggers its own cophonology, (78)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_10e : LinguisticExample :=
  { id := "dolatian2020_10e"
    source := ⟨"dolatian-2020", "(10e)"⟩
    reportedIn := none
    language := "nucl1235"
    primaryText := "amusin-nér"
    discourseSegments := []
    glossedTokens := [("amusin-nér", "husband-PL")]
    translation := "husbands"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dialect", "eastern"), ("suffix", "cInflection"), ("reduction", "none")]
    comment := "Consonant-initial inflection leaves the Prosodic Stem aligned with the morphological stem and the syllable, so only the word-level cophonology applies, in both dialects."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_12a : LinguisticExample :=
  { id := "dolatian2020_12a"
    source := ⟨"dolatian-2020", "(12a)"⟩
    reportedIn := none
    language := "nucl1235"
    primaryText := "zərújt͡sʰ, zərut͡sʰ-él, zərújt͡sʰ-óv"
    discourseSegments := []
    glossedTokens := [("zərújt͡sʰ", "conversation"), ("zərut͡sʰ-él", "conversation-INF"), ("zərújt͡sʰ-óv", "conversation-INST")]
    translation := "conversation; to converse; conversation (instrumental)"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dialect", "eastern"), ("suffix", "vInflection"), ("reduction", "diphthong")]
    comment := "In both dialects the destressed diphthong reduces in derivation and not in inflection; Eastern vowel-initial inflection triggers high vowel reduction but not diphthong reduction, so the Prosodic Stem cophonology lies between the word-level and the stem-level, (76)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_41 : LinguisticExample :=
  { id := "dolatian2020_41"
    source := ⟨"dolatian-2020", "(41)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "darí, darí-k; kaxtní, kaxtní-k; parí, parí-k"
    discourseSegments := []
    glossedTokens := [("darí", "year"), ("darí-k", "year-NMLZ"), ("kaxtní", "secret"), ("kaxtní-k", "secret-NMLZ"), ("parí", "good"), ("parí-k", "good-NMLZ")]
    translation := "year, age; secret (adj.), secret (n.); good, charity"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "derivational"), ("reduction", "none")]
    comment := "A suffix without a full vowel cannot shift stress, so there is no destressed vowel and no reduction."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_42 : LinguisticExample :=
  { id := "dolatian2020_42"
    source := ⟨"dolatian-2020", "(42)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "amusín, amusn-utjún; aznív, aznəv-utjún"
    discourseSegments := []
    glossedTokens := [("amusín", "husband"), ("amusn-utjún", "husband-ness"), ("aznív", "honest"), ("aznəv-utjún", "honest-ness")]
    translation := "husband, marriage; honest, honesty"
    context := ""
    judgment := .acceptable
    alternatives := [("amusən-utjún", .ungrammatical), ("aznv-utjún", .ungrammatical)]
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "derivational"), ("reduction", "both")]
    comment := "Reduction deletes the vowel unless deletion would create an unsyllabifiable cluster, in which case the vowel is replaced by schwa, (46)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_47a : LinguisticExample :=
  { id := "dolatian2020_47a"
    source := ⟨"dolatian-2020", "(47a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "hivánt, hivant-anál; hankíst, hankəst-anál; amusín, amusn-anál"
    discourseSegments := []
    glossedTokens := [("hivánt", "sick"), ("hivant-anál", "sick-INCH"), ("hankíst", "relaxed"), ("hankəst-anál", "relaxed-INCH"), ("amusín", "husband"), ("amusn-anál", "husband-INCH")]
    translation := "sick, to become sick; relaxed, to relax; husband, to marry"
    context := ""
    judgment := .acceptable
    alternatives := [("həvant-anál", .ungrammatical), ("hankist-anál", .ungrammatical), ("amsin-anál", .ungrammatical)]
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "derivational"), ("reduction", "both")]
    comment := "The derivation of (47b): the unstressed high vowel of hivánt does not reduce, the destressed vowel of hankíst reduces to schwa because deletion would leave an unsyllabifiable cluster, and that of amusín deletes."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_48a : LinguisticExample :=
  { id := "dolatian2020_48a"
    source := ⟨"dolatian-2020", "(48a)"⟩
    reportedIn := none
    language := "homs1234"
    primaryText := "ázk, azk-ajín, azk-ajn-agán"
    discourseSegments := []
    glossedTokens := [("ázk", "nation"), ("azk-ajín", "nation-ADJ"), ("azk-ajn-agán", "nation-ADJ-ADJ")]
    translation := "nation; national; nationalist"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dialect", "western"), ("suffix", "derivational"), ("reduction", "deletion")]
    comment := "A destressed high vowel in a suffix reduces too."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_65 : LinguisticExample :=
  { id := "dolatian2020_65"
    source := ⟨"dolatian-2020", "(65)"⟩
    reportedIn := none
    language := "nucl1235"
    primaryText := "tʰúxtʰ, tʰəx.tʰ-í, tʰəx.tʰ-ít͡sʰ, tʰəx.tʰ-óv, tʰəx.tʰ-úm; amusín, amus.n-ú, amus.n-ít͡sʰ, amus.n-óv, amus.n-úm"
    discourseSegments := []
    glossedTokens := [("tʰúxtʰ", "paper"), ("tʰəx.tʰ-í", "paper-DAT"), ("tʰəx.tʰ-óv", "paper-INST"), ("amusín", "husband"), ("amus.n-ú", "husband-DAT"), ("amus.n-óv", "husband-INST")]
    translation := "paper and its case forms; husband and its case forms"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dialect", "eastern"), ("suffix", "vInflection"), ("reduction", "both")]
    comment := "All case suffixes are vowel-initial and Eastern Armenian reduces before each of them, Western Armenian before none: tux.t-í, amusi.n-óv."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_66 : LinguisticExample :=
  { id := "dolatian2020_66"
    source := ⟨"dolatian-2020", "(66)"⟩
    reportedIn := none
    language := "nucl1235"
    primaryText := "tʰəx.tʰ-ér, tʰəx.tʰ-er-óv; amusin.-nér, amusin.-ner-óv"
    discourseSegments := []
    glossedTokens := [("tʰəx.tʰ-ér", "paper-PL"), ("tʰəx.tʰ-er-óv", "paper-PL-INST"), ("amusin.-nér", "husband-PL"), ("amusin.-ner-óv", "husband-PL-INST")]
    translation := "papers, with papers; husbands, with husbands"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dialect", "eastern"), ("suffix", "plural"), ("reduction", "both")]
    comment := "The plural is -er after monosyllabic bases and -ner after polysyllabic ones; the vowel-initial allomorph reduces the base and the consonant-initial one does not, whatever case follows."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_72 : LinguisticExample :=
  { id := "dolatian2020_72"
    source := ⟨"dolatian-2020", "(72)"⟩
    reportedIn := none
    language := "nucl1235"
    primaryText := "manúk, mank-akán, mank-án, manuk-í; lúrd͡ʒ, lərd͡ʒ-anál, lurd͡ʒ-í; fílm, film-ajín, film-ér"
    discourseSegments := []
    glossedTokens := [("manúk", "child"), ("mank-akán", "child-ish"), ("mank-án", "child-GEN.irregular"), ("manuk-í", "child-GEN.regular"), ("lúrd͡ʒ", "serious"), ("lərd͡ʒ-anál", "serious-INCH"), ("lurd͡ʒ-í", "serious-GEN"), ("fílm", "film"), ("film-ajín", "film-ADJ"), ("film-ér", "film-PL")]
    translation := "child, childish, child's; serious, to get serious, of the serious one; film, cinematic, films"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("dialect", "eastern"), ("suffix", "vInflection"), ("reduction", "none")]
    comment := "Pre-inflectional reduction does not apply in regularized inflection, inflected adjectives or loanwords: it is a lexical process and not a post-cyclic word-level one, against the recursive prosodic word analysis of §2.5.3.2."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def all : List LinguisticExample := [ex_1, ex_2, ex_3b, ex_4, ex_5a, ex_5c, ex_7a, ex_7b, ex_10c, ex_10e, ex_12a, ex_41, ex_42, ex_47a, ex_48a, ex_65, ex_66, ex_72]

end Dolatian2020.Examples
