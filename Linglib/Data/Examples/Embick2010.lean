import Linglib.Data.Examples.Schema

/-!
# `Embick2010` — typed example data

Auto-generated from `Linglib/Data/Examples/Embick2010.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Embick2010.Examples`.
-/

namespace Embick2010.Examples

open Data.Examples

def amavi : LinguisticExample :=
  { id := "embick2010_amavi"
    source := ⟨"embick-2010", "(3), (10a)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "amā-v-ī"
    discourseSegments := []
    glossedTokens := []
    translation := "I loved"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "AM"), ("h1", "v"), ("h1exp", ""), ("h2", "theme"), ("h2exp", "-ā"), ("h3", "aspect"), ("h3exp", "-vi"), ("h4", "tense"), ("h4exp", ""), ("h5", "agr"), ("h5exp", "-ī"), ("target", "5"), ("conditioner", "3"), ("claim", "attested")]
    comment := "Perfect indicative: null T[pres] is pruned, Agr is concatenated with Asp[perf] and takes the special -ī."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def amavisti : LinguisticExample :=
  { id := "embick2010_amavisti"
    source := ⟨"embick-2010", "(3)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "amā-v-istī"
    discourseSegments := []
    glossedTokens := []
    translation := "you loved"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "AM"), ("h1", "v"), ("h1exp", ""), ("h2", "theme"), ("h2exp", "-ā"), ("h3", "aspect"), ("h3exp", "-vi"), ("h4", "tense"), ("h4exp", ""), ("h5", "agr"), ("h5exp", "-istī"), ("target", "5"), ("conditioner", "3"), ("claim", "attested")]
    comment := "Perfect indicative 2sg: the special -istī next to Asp[perf]."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def amaveram : LinguisticExample :=
  { id := "embick2010_amaveram"
    source := ⟨"embick-2010", "(3), (10b)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "amā-ve-rā-m"
    discourseSegments := []
    glossedTokens := []
    translation := "I had loved"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "AM"), ("h1", "v"), ("h1exp", ""), ("h2", "theme"), ("h2exp", "-ā"), ("h3", "aspect"), ("h3exp", "-vi"), ("h4", "tense"), ("h4exp", "-sā"), ("h5", "agr"), ("h5exp", "-m"), ("target", "5"), ("conditioner", "3"), ("claim", "blocked")]
    comment := "Pluperfect: overt T between Asp[perf] and Agr, so the elsewhere -m."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def amaverim : LinguisticExample :=
  { id := "embick2010_amaverim"
    source := ⟨"embick-2010", "(3)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "amā-ve-rī-m"
    discourseSegments := []
    glossedTokens := []
    translation := "I have loved (subjunctive)"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "AM"), ("h1", "v"), ("h1exp", ""), ("h2", "theme"), ("h2exp", "-ā"), ("h3", "aspect"), ("h3exp", "-vi"), ("h4", "tense"), ("h4exp", "-sī"), ("h5", "agr"), ("h5exp", "-m"), ("target", "5"), ("conditioner", "3"), ("claim", "blocked")]
    comment := "Perfect subjunctive: overt T intervenes."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def amavero : LinguisticExample :=
  { id := "embick2010_amavero"
    source := ⟨"embick-2010", "(3)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "amā-ve-r-ō"
    discourseSegments := []
    glossedTokens := []
    translation := "I will have loved"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "AM"), ("h1", "v"), ("h1exp", ""), ("h2", "theme"), ("h2exp", "-ā"), ("h3", "aspect"), ("h3exp", "-vi"), ("h4", "tense"), ("h4exp", "-si"), ("h5", "agr"), ("h5exp", "-ō"), ("target", "5"), ("conditioner", "3"), ("claim", "blocked")]
    comment := "Future perfect: overt T intervenes."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def capimus : LinguisticExample :=
  { id := "embick2010_capimus"
    source := ⟨"embick-2010", "(17)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "cap-i-mus"
    discourseSegments := []
    glossedTokens := []
    translation := "we take"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "CAP"), ("h1", "v"), ("h1exp", ""), ("h2", "theme"), ("h2exp", "-i"), ("target", "2"), ("conditioner", "root"), ("claim", "attested")]
    comment := "The theme sees the root's conjugation feature across the pruned v."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def capessimus_root : LinguisticExample :=
  { id := "embick2010_capessimus_root"
    source := ⟨"embick-2010", "(18)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "cap-ess-i-mus"
    discourseSegments := []
    glossedTokens := []
    translation := "we take eagerly"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "CAP"), ("h1", "v"), ("h1exp", "-ess"), ("h2", "theme"), ("h2exp", "-i"), ("target", "2"), ("conditioner", "root"), ("claim", "blocked")]
    comment := "The overt desiderative v intervenes: the theme cannot see the root's class."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def capessimus_v : LinguisticExample :=
  { id := "embick2010_capessimus_v"
    source := ⟨"embick-2010", "(18)"⟩
    reportedIn := none
    language := "lati1261"
    primaryText := "cap-ess-i-mus"
    discourseSegments := []
    glossedTokens := []
    translation := "we take eagerly"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "CAP"), ("h1", "v"), ("h1exp", "-ess"), ("h2", "theme"), ("h2exp", "-i"), ("target", "2"), ("conditioner", "1"), ("claim", "attested")]
    comment := "The theme sees the class feature of the exponent it is concatenated with, -ess[III]."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def marriage : LinguisticExample :=
  { id := "embick2010_marriage"
    source := ⟨"embick-2010", "(31)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "marri-age"
    discourseSegments := []
    glossedTokens := []
    translation := "marriage"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "MARRY"), ("h1", "n"), ("h1exp", "-age"), ("target", "1"), ("conditioner", "root"), ("claim", "attested")]
    comment := "Root-attached n: Root-determined -age."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def marrying : LinguisticExample :=
  { id := "embick2010_marrying"
    source := ⟨"embick-2010", "(31), (50)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "marry-ing"
    discourseSegments := []
    glossedTokens := []
    translation := "marrying"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "MARRY"), ("h1", "v"), ("h1exp", ""), ("h2", "n"), ("h2exp", "-ing"), ("target", "2"), ("conditioner", "root"), ("claim", "blocked")]
    comment := "Gerund: the Root is not present in the cycle in which n is spelled out."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bent : LinguisticExample :=
  { id := "embick2010_bent"
    source := ⟨"embick-2010", "(34)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "ben-t"
    discourseSegments := []
    glossedTokens := []
    translation := "bent"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "BEND"), ("h1", "v"), ("h1exp", ""), ("h2", "tense"), ("h2exp", "-t"), ("target", "2"), ("conditioner", "root"), ("claim", "attested")]
    comment := "Noncyclic T[past] sees the Root across the pruned v."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def oxen : LinguisticExample :=
  { id := "embick2010_oxen"
    source := ⟨"embick-2010", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "ox-en"
    discourseSegments := []
    glossedTokens := []
    translation := "oxen"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "OX"), ("h1", "n"), ("h1exp", ""), ("h2", "number"), ("h2exp", "-en"), ("target", "2"), ("conditioner", "root"), ("claim", "attested")]
    comment := "Noncyclic [pl] sees the Root across the pruned n."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def breakability : LinguisticExample :=
  { id := "embick2010_breakability"
    source := ⟨"embick-2010", "(36)–(37)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "break-abil-ity"
    discourseSegments := []
    glossedTokens := []
    translation := "breakability"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "BREAK"), ("h1", "a"), ("h1exp", "-able"), ("h2", "n"), ("h2exp", "-ity"), ("target", "2"), ("conditioner", "1"), ("claim", "attested")]
    comment := "Potentiation: n sees the a realized as -able."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def colorization_v : LinguisticExample :=
  { id := "embick2010_colorization_v"
    source := ⟨"embick-2010", "(49)–(53)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "color-iz-ation"
    discourseSegments := []
    glossedTokens := []
    translation := "colorization"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "COLOR"), ("h1", "v"), ("h1exp", "-ize"), ("h2", "n"), ("h2exp", "-ation"), ("target", "2"), ("conditioner", "1"), ("claim", "attested")]
    comment := "Outer n sees the v realized as -ize, which conditions -ation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def colorization_root : LinguisticExample :=
  { id := "embick2010_colorization_root"
    source := ⟨"embick-2010", "(49)–(53)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "color-iz-ation"
    discourseSegments := []
    glossedTokens := []
    translation := "colorization"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "COLOR"), ("h1", "v"), ("h1exp", "-ize"), ("h2", "n"), ("h2exp", "-ation"), ("target", "2"), ("conditioner", "root"), ("claim", "blocked")]
    comment := "Outer n cannot see the Root."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bachaanaa : LinguisticExample :=
  { id := "embick2010_bachaanaa"
    source := ⟨"embick-2010", "(22b), (23)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "bach-aa-naa"
    discourseSegments := []
    glossedTokens := []
    translation := "save"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "BACH"), ("h1", "v"), ("h1exp", ""), ("h2", "voice"), ("h2exp", "-aa"), ("target", "2"), ("conditioner", "root"), ("claim", "attested")]
    comment := "Transitive: noncyclic Voice[ag] shows Root-determined -aa vs -Ø."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bachvaanaa : LinguisticExample :=
  { id := "embick2010_bachvaanaa"
    source := ⟨"embick-2010", "(25b), (26)"⟩
    reportedIn := none
    language := "hind1269"
    primaryText := "bach-vaa-naa"
    discourseSegments := []
    glossedTokens := []
    translation := "have saved"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "BACH"), ("h1", "v"), ("h1exp", ""), ("h2", "voicePassive"), ("h2exp", "-v"), ("h3", "v"), ("h3exp", ""), ("h4", "voice"), ("h4exp", "-aa"), ("target", "4"), ("conditioner", "root"), ("claim", "blocked")]
    comment := "Indirect causative: the outer Voice[ag] is two cycles up, so the default -aa."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [amavi, amavisti, amaveram, amaverim, amavero, capimus, capessimus_root, capessimus_v, marriage, marrying, bent, oxen, breakability, colorization_v, colorization_root, bachaanaa, bachvaanaa]

end Embick2010.Examples
