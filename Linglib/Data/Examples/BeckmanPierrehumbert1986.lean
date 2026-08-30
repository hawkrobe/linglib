import Linglib.Data.Examples.Schema

/-!
# `BeckmanPierrehumbert1986` — typed example data

Auto-generated from `Linglib/Data/Examples/BeckmanPierrehumbert1986.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BeckmanPierrehumbert1986.Examples`.
-/

namespace BeckmanPierrehumbert1986.Examples

open Data.Examples

def bp1986_fig3 : LinguisticExample :=
  { id := "bp1986_fig3"
    source := ⟨"beckman-pierrehumbert-1986", "Fig. 3"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Kore-wa toriya-no mawari-no oma'warisan-no hanasi desu."
    discourseSegments := []
    glossedTokens := [("Kore-wa", "this-TOP"), ("toriya-no", "bird.shop-GEN"), ("mawari-no", "vicinity-GEN"), ("oma'warisan-no", "policeman-GEN"), ("hanasi", "story"), ("desu", "COP")]
    translation := "This is a story about the policeman near the bird shop."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("accentual phrase", "unaccented"), ("tonal pattern", "phrasal H ... boundary L")]
    comment := "The long unaccented AP shows smooth interpolation from phrasal H to boundary L — no H-tone spreading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bp1986_fig5 : LinguisticExample :=
  { id := "bp1986_fig5"
    source := ⟨"beckman-pierrehumbert-1986", "Fig. 5"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Kore-wa mo'riya-no mawari-no oma'warisan-no hanasi desu."
    discourseSegments := []
    glossedTokens := [("Kore-wa", "this-TOP"), ("mo'riya-no", "Moriya-GEN"), ("mawari-no", "vicinity-GEN"), ("oma'warisan-no", "policeman-GEN"), ("hanasi", "story"), ("desu", "COP")]
    translation := "This is a story about the policeman near Moriya."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("accentual phrase", "accented"), ("process", "catathesis")]
    comment := "The boundary L after the accented phrase is realized much lower: catathesis triggered by the accent."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bp1986_fig6a : LinguisticExample :=
  { id := "bp1986_fig6a"
    source := ⟨"beckman-pierrehumbert-1986", "Fig. 6a"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Uma'i mame'-wa arimasen."
    discourseSegments := []
    glossedTokens := [("Uma'i", "delicious"), ("mame'-wa", "bean-TOP"), ("arimasen", "exist.NEG.POL")]
    translation := "There are no delicious beans."
    context := "Adjective and noun grouped in one accentual phrase."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("process", "accent deletion"), ("constraint", "one accent per AP")]
    comment := "Grouping two accented words into one AP deletes the second accent; the contour equals Fig. 6b's."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bp1986_fig6b : LinguisticExample :=
  { id := "bp1986_fig6b"
    source := ⟨"beckman-pierrehumbert-1986", "Fig. 6b"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Uma'i ame-wa arimasen."
    discourseSegments := []
    glossedTokens := [("Uma'i", "delicious"), ("ame-wa", "candy-TOP"), ("arimasen", "exist.NEG.POL")]
    translation := "There is no delicious candy."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("accentual phrase", "one accent"), ("noun", "unaccented")]
    comment := "Identical tonal contour to Fig. 6a — deletion neutralizes the mame'/ame accent contrast under grouping."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bp1986_fig8 : LinguisticExample :=
  { id := "bp1986_fig8"
    source := ⟨"beckman-pierrehumbert-1986", "Fig. 8"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Amai mame'-wa arimasen."
    discourseSegments := []
    glossedTokens := [("Amai", "sweet"), ("mame'-wa", "bean-TOP"), ("arimasen", "exist.NEG.POL")]
    translation := "There are no sweet beans."
    context := "Contrastive emphasis on amai."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("focus", "initial"), ("process", "subordination or dephrasing")]
    comment := "Focus on the unaccented adjective flattens the following accented noun's rise — extreme subordination is phonetically like dephrasing."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bp1986_ex2 : LinguisticExample :=
  { id := "bp1986_ex2"
    source := ⟨"beckman-pierrehumbert-1986", "(2)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Kono arai ayaori-no obizi ga."
    discourseSegments := []
    glossedTokens := [("Kono", "this"), ("arai", "rough"), ("ayaori-no", "twill-GEN"), ("obizi", "obi.cloth"), ("ga", "NOM")]
    translation := "This rough twill obi-cloth."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("intermediate phrase", "break after first modifier")]
    comment := "Most subjects split this into two intermediate phrases — smaller than an English intonation phrase."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bp1986_ex3 : LinguisticExample :=
  { id := "bp1986_ex3"
    source := ⟨"beckman-pierrehumbert-1986", "(3)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "be'ika neage hantai u'ndoo"
    discourseSegments := []
    glossedTokens := [("be'ika", "rice.price"), ("neage", "price.raise"), ("hantai", "protest"), ("u'ndoo", "movement")]
    translation := "movement protesting rice-price increases"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("intermediate phrase", "break inside compound")]
    comment := "Catathesis blocked after neage: an ip boundary can fall inside a compound in Japanese."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bp1986_fig36 : LinguisticExample :=
  { id := "bp1986_fig36"
    source := ⟨"beckman-pierrehumbert-1986", "Fig. 36"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "Moo tyotto migigawa-ga sagerare'ru."
    discourseSegments := []
    glossedTokens := [("Moo", "more"), ("tyotto", "a.little"), ("migigawa-ga", "right.side-NOM"), ("sagerare'ru", "can.be.lowered")]
    translation := "The right side can be lowered a little more."
    context := "Declarative vs yes/no question renditions."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("process", "final lowering"), ("domain", "declaratives only")]
    comment := "Declarative and interrogative F0 match early and diverge at the end: final lowering in declaratives."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bp1986_fig1 : LinguisticExample :=
  { id := "bp1986_fig1"
    source := ⟨"beckman-pierrehumbert-1986", "Fig. 1"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "an orange ballgown"
    discourseSegments := []
    glossedTokens := []
    translation := "an orange ballgown"
    context := "Answers to the question: What's that?"
    judgment := .acceptable
    alternatives := []
    readings := [("H* H* L L%: neutral declarative", .acceptable), ("H*+L H* L L%: downstepping, feigned judiciousness", .acceptable), ("L* H* L L%: surprise-redundancy", .acceptable)]
    paperFeatures := [("accent inventory", "postlexical shape choice")]
    comment := "Accent shape contrasts intonational meanings, never lexical items."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bp1986_fig2 : LinguisticExample :=
  { id := "bp1986_fig2"
    source := ⟨"beckman-pierrehumbert-1986", "Fig. 2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I really won't allow Mary."
    discourseSegments := []
    glossedTokens := []
    translation := "I really won't allow Mary."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("H* on Mary: peak near end of stressed syllable, impatient reassertion", .acceptable), ("H+L* on Mary: peak just before the stressed syllable, peevish", .acceptable)]
    paperFeatures := [("diagnostic", "peak alignment"), ("claim", "bitonal accents are units")]
    comment := "The unstarred H of H+L* lands mid-word in Marianna — implausible as any phrasal tone."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bp1986_fig11 : LinguisticExample :=
  { id := "bp1986_fig11"
    source := ⟨"beckman-pierrehumbert-1986", "Fig. 11"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "blueberries, boysberries, raspberries, mulberries and brambleberries"
    discourseSegments := []
    glossedTokens := []
    translation := "blueberries, boysberries, raspberries, mulberries and brambleberries"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("process", "catathesis chain"), ("contour", "descending staircase")]
    comment := "Iterated catathesis: up to six or seven step levels, ruling out a fixed mid tone."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bp1986_ex4 : LinguisticExample :=
  { id := "bp1986_ex4"
    source := ⟨"beckman-pierrehumbert-1986", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "'I' means insert."
    discourseSegments := []
    glossedTokens := []
    translation := "'I' means insert."
    context := "A text-editor tutor defining a key."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("intermediate phrase", "medial L phrase accent")]
    comment := "The definiendum is set off as its own intermediate phrase; a full intonation break would be too strong."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bp1986_ex7 : LinguisticExample :=
  { id := "bp1986_ex7"
    source := ⟨"beckman-pierrehumbert-1986", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They gave orange marmalade, lemon-oil marmalade, and watermelon-rind marmalade?"
    discourseSegments := []
    glossedTokens := []
    translation := "They gave orange marmalade, lemon-oil marmalade, and watermelon-rind marmalade?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("intermediate phrase", "H phrase accent per list item"), ("boundary tone", "one final H%")]
    comment := "Three H-phrase-accent ips under one intonation phrase whose single H% closes the list."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bp1986_ex9 : LinguisticExample :=
  { id := "bp1986_ex9"
    source := ⟨"beckman-pierrehumbert-1986", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A pale orange and yellow ballgown."
    discourseSegments := []
    glossedTokens := []
    translation := "A pale orange and yellow ballgown."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("pale | orange and yellow: both conjuncts pale", .acceptable), ("pale orange | and yellow: only the orange pale", .acceptable)]
    paperFeatures := [("intermediate phrase", "scope disambiguation")]
    comment := "Intermediate phrasing disambiguates the scope of the modifier over the conjunction."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bp1986_fig34 : LinguisticExample :=
  { id := "bp1986_fig34"
    source := ⟨"beckman-pierrehumbert-1986", "Fig. 34"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "it's eleven and nine and one and EIGHTY"
    discourseSegments := []
    glossedTokens := []
    translation := "it's eleven and nine and one and EIGHTY"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("process", "catathesis blocked at focus"), ("intermediate phrase", "break before focus")]
    comment := "Downstepping accents on the first three numbers; the focused item is set off by an ip boundary that resets the range."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [bp1986_fig3, bp1986_fig5, bp1986_fig6a, bp1986_fig6b, bp1986_fig8, bp1986_ex2, bp1986_ex3, bp1986_fig36, bp1986_fig1, bp1986_fig2, bp1986_fig11, bp1986_ex4, bp1986_ex7, bp1986_ex9, bp1986_fig34]

end BeckmanPierrehumbert1986.Examples
