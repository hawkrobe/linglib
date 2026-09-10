import Linglib.Data.Examples.Schema

/-!
# `Grubic2015` — typed example data

Auto-generated from `Linglib/Data/Examples/Grubic2015.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Grubic2015.Examples`.
-/

namespace Grubic2015.Examples

open Data.Examples

def ex_6_24 : LinguisticExample :=
  { id := "grubic2015_6_24"
    source := ⟨"grubic-2015", "(24)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Ne sakatari yak'i."
    discourseSegments := []
    glossedTokens := [("Ne", "1SG.DEP"), ("sakatari", "secretary"), ("yak'i.", "only")]
    translation := "I'm only a secretary."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("complement exclusion: I am nothing else in addition", .acceptable), ("rank order: I am nothing better", .acceptable)]
    paperFeatures := [("particle", "yak"), ("configuration", "predicate")]
    comment := "Both readings carry a mirative component: more, or something more prestigious, was expected."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_6_25a : LinguisticExample :=
  { id := "grubic2015_6_25a"
    source := ⟨"grubic-2015", "(25a)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Salko bano=i Dimza yak'i."
    discourseSegments := []
    glossedTokens := [("Salko", "build.PFV"), ("bano=i", "house=BM"), ("Dimza", "Dimza"), ("yak'i.", "only")]
    translation := "Only Dimza built a house."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "yak"), ("configuration", "markedSubjectFocus"), ("inference", "Dimza built a house"), ("inference", "nobody else built a house")]
    comment := "Consultant: Dimza built a house, and nobody else built a house."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_6_25b : LinguisticExample :=
  { id := "grubic2015_6_25b"
    source := ⟨"grubic-2015", "(25b)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Salko bano=i Dimza yak'i bu."
    discourseSegments := []
    glossedTokens := [("Salko", "build.PFV"), ("bano=i", "house=BM"), ("Dimza", "Dimza"), ("yak'i", "only"), ("bu.", "NEG")]
    translation := "Not only Dimza built a house."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "yak"), ("configuration", "markedSubjectFocus"), ("inference", "Dimza built a house"), ("inference", "other people also built a house")]
    comment := "The exclusive component is asserted; the prejacent projects through negation."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_6_25c : LinguisticExample :=
  { id := "grubic2015_6_25c"
    source := ⟨"grubic-2015", "(25c)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Salko bano=i Dimza yak'i ɗo?"
    discourseSegments := []
    glossedTokens := [("Salko", "build.PFV"), ("bano=i", "house=BM"), ("Dimza", "Dimza"), ("yak'i", "only"), ("ɗo?", "Q")]
    translation := "Did only Dimza build a house?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "yak"), ("configuration", "markedSubjectFocus"), ("inference", "Dimza built a house")]
    comment := "Consultant: Dimza built a house, and you want to confirm: alone or with other people?"
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_6_26 : LinguisticExample :=
  { id := "grubic2015_6_26"
    source := ⟨"grubic-2015", "(26)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Esha=i Sama yak'i nzono, ke esha Hawwa nzono."
    discourseSegments := []
    glossedTokens := [("Esha=i", "call.PFV=BM"), ("Sama", "Sama"), ("yak'i", "only"), ("nzono,", "yesterday"), ("ke", "also"), ("esha", "call.PFV"), ("Hawwa", "Hawwa"), ("nzono.", "yesterday")]
    translation := "He only called Sama yesterday, and he also called Hawwa yesterday."
    context := "Who did Njelu call yesterday?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "yak"), ("configuration", "markedObjectFocus")]
    comment := "The exclusive component is not cancellable."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_6_28 : LinguisticExample :=
  { id := "grubic2015_6_28"
    source := ⟨"grubic-2015", "(28)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Ne'e yak ne wa ampani yam ki korino bu."
    discourseSegments := []
    glossedTokens := [("Ne'e", "1SG"), ("yak", "only"), ("ne", "1SG"), ("wa", "get.PFV"), ("ampani", "harvest"), ("yam", "a.lot"), ("ki", "at"), ("korino", "farm=1SG.POSS"), ("bu.", "NEG")]
    translation := "I didn't only get a good harvest."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "yak"), ("configuration", "predicate")]
    comment := "The mirative component projects: odd because a good harvest is not less than expected."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_6_140 : LinguisticExample :=
  { id := "grubic2015_6_140"
    source := ⟨"grubic-2015", "(140)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Kule yak salko bano mano."
    discourseSegments := []
    glossedTokens := [("Kule", "Kule"), ("yak", "only"), ("salko", "build.PFV"), ("bano", "house"), ("mano.", "last.year")]
    translation := "Kule only built a house last year."
    context := "Kule wanted to build a house and a granary last year."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "yak"), ("configuration", "unmarkedObjectFocus")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_6_145a : LinguisticExample :=
  { id := "grubic2015_6_145a"
    source := ⟨"grubic-2015", "(145a)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "O'o, Kule yak onto agoggo."
    discourseSegments := []
    glossedTokens := [("O'o,", "no"), ("Kule", "Kule"), ("yak", "only"), ("onto", "give.PFV.3SG.F"), ("agoggo.", "watch")]
    translation := "No, Kule only gave a watch to her."
    context := "Did Kule give a watch to Dimza and Jajei?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "yak"), ("configuration", "dependentPronoun")]
    comment := "Reinterpreted with the exclusive associating with the direct object: Jajei is expecting a watch and other things."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_6_145b : LinguisticExample :=
  { id := "grubic2015_6_145b"
    source := ⟨"grubic-2015", "(145b)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "O'o, Kule onko agoggo=i ki te yak'i."
    discourseSegments := []
    glossedTokens := [("O'o,", "no"), ("Kule", "Kule"), ("onko", "give.PFV"), ("agoggo=i", "watch=BM"), ("ki", "to"), ("te", "3SG.F"), ("yak'i.", "only")]
    translation := "No, Kule only gave a watch to her."
    context := "Did Kule give a watch to Dimza and Jajei?"
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("particle", "yak"), ("configuration", "independentPronoun")]
    comment := "Marginal because it is hard to tell who te refers to without intermediate discussion of Jajei."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_6_148a : LinguisticExample :=
  { id := "grubic2015_6_148a"
    source := ⟨"grubic-2015", "(148a)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Hawwa=s, ne moishe Daho a esha=i te yak'i."
    discourseSegments := []
    glossedTokens := [("Hawwa=s,", "Hawwa=DEF.DET.F"), ("ne", "1SG"), ("moishe", "see.HAB"), ("Daho", "Daho"), ("a", "3SG.HAB"), ("esha=i", "call.HAB=BM"), ("te", "3SG.F"), ("yak'i.", "only")]
    translation := "Hawwa, I think Daho only calls her."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("the only person that Daho calls is Hawwa", .acceptable)]
    paperFeatures := [("particle", "yak"), ("configuration", "resumptivePronoun")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_6_148b : LinguisticExample :=
  { id := "grubic2015_6_148b"
    source := ⟨"grubic-2015", "(148b)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Hawwa=s, ne moishe Daho a esha yak'i."
    discourseSegments := []
    glossedTokens := [("Hawwa=s,", "Hawwa=DEF.DET.F"), ("ne", "1SG"), ("moishe", "see.HAB"), ("Daho", "Daho"), ("a", "3SG.HAB"), ("esha", "call.HAB"), ("yak'i.", "only")]
    translation := "Hawwa, I think Daho only calls."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("the only person that Daho calls is Hawwa", .unacceptable), ("Daho does nothing but call", .acceptable)]
    paperFeatures := [("particle", "yak"), ("configuration", "topicalizedGap")]
    comment := "The exclusive cannot associate with the moved constituent."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_6_149 : LinguisticExample :=
  { id := "grubic2015_6_149"
    source := ⟨"grubic-2015", "(149)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Hawwa=s, ne moishe Daho lei ki tomiya a esha."
    discourseSegments := []
    glossedTokens := [("Hawwa=s,", "Hawwa=DEF.DET.F"), ("ne", "1SG"), ("moishe", "see.HAB"), ("Daho", "Daho"), ("lei", "at"), ("ki", "any"), ("tomiya", "time"), ("a", "3SG.HAB"), ("esha.", "call.HAB")]
    translation := "Hawwa, I think Daho always calls."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("whenever Daho calls somebody, she calls Hawwa", .acceptable)]
    paperFeatures := [("particle", "leiKiTomiya"), ("configuration", "topicalizedGap")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_6_150a : LinguisticExample :=
  { id := "grubic2015_6_150a"
    source := ⟨"grubic-2015", "(150a)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Hasha hoti maɗɗi a esha Lakka, Gamba me esha=i te yak'i."
    discourseSegments := []
    glossedTokens := [("Hasha", "Hasha"), ("hoti", "day"), ("maɗɗi", "some"), ("a", "3SG.HAB"), ("esha", "call.HAB"), ("Lakka,", "Lakka"), ("Gamba", "Gamba"), ("me", "but"), ("esha=i", "call.HAB=BM"), ("te", "3SG.F"), ("yak'i.", "only")]
    translation := "Hasha sometimes calls Lakka, and Gambo only calls her."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "yak"), ("configuration", "focusedPronoun")]
    comment := "Consultant: he always calls only her, never anybody else."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_6_150b : LinguisticExample :=
  { id := "grubic2015_6_150b"
    source := ⟨"grubic-2015", "(150b)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Hasha hoti maɗɗi a esha Lakka, Gambo me a esha yak'i."
    discourseSegments := []
    glossedTokens := [("Hasha", "Hasha"), ("hoti", "day"), ("maɗɗi", "some"), ("a", "3SG.HAB"), ("esha", "call.HAB"), ("Lakka,", "Lakka"), ("Gambo", "Gamba"), ("me", "but"), ("a", "3SG.HAB"), ("esha", "call.HAB"), ("yak'i.", "only")]
    translation := "Hasha sometimes calls Lakka, and Gambo only calls her."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("particle", "yak"), ("configuration", "elidedPronoun")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_6_151 : LinguisticExample :=
  { id := "grubic2015_6_151"
    source := ⟨"grubic-2015", "(151)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Hasha hoti maɗɗi a esha Lakka, Gambo me lei ki tomiya a esha."
    discourseSegments := []
    glossedTokens := [("Hasha", "Hasha"), ("hoti", "day"), ("maɗɗi", "some"), ("a", "3SG.HAB"), ("esha", "call.HAB"), ("Lakka,", "Lakka"), ("Gambo", "Gamba"), ("me", "but"), ("lei", "at"), ("ki", "any"), ("tomiya", "time"), ("a", "3SG.HAB"), ("esha.", "call.HAB")]
    translation := "Hasha sometimes calls Lakka, and Gambo always does."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "leiKiTomiya"), ("configuration", "elidedPronoun")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_6_153 : LinguisticExample :=
  { id := "grubic2015_6_153"
    source := ⟨"grubic-2015", "(153)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Biya ma maranko shinkafa a tishe yak'i."
    discourseSegments := []
    glossedTokens := [("Biya", "people"), ("ma", "REL"), ("maranko", "farm.PL.PFV"), ("shinkafa", "rice"), ("a", "3SG.HAB"), ("tishe", "eat.HAB"), ("yak'i.", "only")]
    translation := "People that grow rice only eat it."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("they don't sell it or give it out", .acceptable), ("they eat nothing else", .unacceptable)]
    paperFeatures := [("particle", "yak"), ("configuration", "elidedObject")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_6_158 : LinguisticExample :=
  { id := "grubic2015_6_158"
    source := ⟨"grubic-2015", "(158)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Samaye gitkok tishe=i jarabawa=to yak'i."
    discourseSegments := []
    glossedTokens := [("Samaye", "Samaye"), ("gitkok", "be.able.PFV.TOT"), ("tishe=i", "eat.HAB=BM"), ("jarabawa=to", "exam=3SG.F.POSS"), ("yak'i.", "only")]
    translation := "Samaye only managed to pass her exams."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "yak"), ("configuration", "presupposition")]
    comment := "The exclusive does not associate with the presupposition of gitko."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_6_159 : LinguisticExample :=
  { id := "grubic2015_6_159"
    source := ⟨"grubic-2015", "(159)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Samaye lei ki tomiya a gishentik tina=i jarabawa=to."
    discourseSegments := []
    glossedTokens := [("Samaye", "Samaye"), ("lei", "at"), ("ki", "any"), ("tomiya", "time"), ("a", "3SG.HAB"), ("gishentik", "be.able.HAB.TOT"), ("tina=i", "eat.FUT=BM"), ("jarabawa=to.", "exam=3SG.F.POSS")]
    translation := "Samaye always manages to pass her exams."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("whenever she tries, she passes", .acceptable)]
    paperFeatures := [("particle", "leiKiTomiya"), ("configuration", "presupposition")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_6_160 : LinguisticExample :=
  { id := "grubic2015_6_160"
    source := ⟨"grubic-2015", "(160)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Si onko agoggo=i ki Shuwa, si ke ono."
    discourseSegments := []
    glossedTokens := [("Si", "3SG.M"), ("onko", "give.PFV"), ("agoggo=i", "watch=BM"), ("ki", "to"), ("Shuwa,", "Shuwa"), ("si", "3SG.M"), ("ke", "also"), ("ono.", "give.1SG.DEP")]
    translation := "He gave a watch to Shuwa, and he also gave it to me."
    context := "Whom did Kule give a watch?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "ke"), ("configuration", "dependentPronoun")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_6_162a : LinguisticExample :=
  { id := "grubic2015_6_162a"
    source := ⟨"grubic-2015", "(162a)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Kule esha=i Dimza, ke esha=i ne'e."
    discourseSegments := []
    glossedTokens := [("Kule", "Kule"), ("esha=i", "call.PFV=BM"), ("Dimza,", "Dimza"), ("ke", "also"), ("esha=i", "call.PFV=BM"), ("ne'e.", "1SG")]
    translation := "Kule called Dimza and he also called me."
    context := "Whom did Kule call?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "ke"), ("configuration", "independentPronoun")]
    comment := "Rejected in favour of a dependent pronoun with a totality-extended verb."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_6_162b : LinguisticExample :=
  { id := "grubic2015_6_162b"
    source := ⟨"grubic-2015", "(162b)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Kule esha=i Dimza ke eshino."
    discourseSegments := []
    glossedTokens := [("Kule", "Kule"), ("esha=i", "call.PFV=BM"), ("Dimza", "Dimza"), ("ke", "also"), ("eshino.", "call.PFV.TOT.1SG")]
    translation := "Kule called Dimza and he also called me."
    context := "Whom did Kule call?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "ke"), ("configuration", "dependentPronoun")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_6_163 : LinguisticExample :=
  { id := "grubic2015_6_163"
    source := ⟨"grubic-2015", "(163)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Ke salko bano."
    discourseSegments := []
    glossedTokens := [("Ke", "also"), ("salko", "build.PFV"), ("bano.", "house")]
    translation := "He also built a house."
    context := "I know that Hawwa built a house, but what about Kule? What did he build?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "ke"), ("configuration", "elidedTopicalSubject")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_6_164 : LinguisticExample :=
  { id := "grubic2015_6_164"
    source := ⟨"grubic-2015", "(164)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Kule onko agoggo=i ki Shuwa, ke har ono."
    discourseSegments := []
    glossedTokens := [("Kule", "Kule"), ("onko", "give.PFV"), ("agoggo=i", "watch=BM"), ("ki", "to"), ("Shuwa,", "Shuwa"), ("ke", "and"), ("har", "even"), ("ono.", "give.PFV.1SG.DEP")]
    translation := "Kule gave a watch to Shuwa, and he even gave one to me."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "har"), ("configuration", "dependentPronoun")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_6_165 : LinguisticExample :=
  { id := "grubic2015_6_165"
    source := ⟨"grubic-2015", "(165)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Hawwa salko bano, Kule ke salko bano."
    discourseSegments := []
    glossedTokens := [("Hawwa", "Hawwa"), ("salko", "build.PFV"), ("bano,", "house"), ("Kule", "Kule"), ("ke", "also"), ("salko", "build.PFV"), ("bano.", "house")]
    translation := "Hawwa built a house, and Kule also built a house."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "ke"), ("configuration", "preverbalSubject")]
    comment := "Preverbal subjects are out of focus, which the exclusive cannot associate with."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_6_166 : LinguisticExample :=
  { id := "grubic2015_6_166"
    source := ⟨"grubic-2015", "(166)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Dimza yak salko bano."
    discourseSegments := []
    glossedTokens := [("Dimza", "Dimza"), ("yak", "only"), ("salko", "build.PFV"), ("bano.", "house")]
    translation := "Dimza only built a house."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "yak"), ("configuration", "unmarkedObjectFocus"), ("inference", "Dimza didn't build anything else"), ("inference", "he was expected to build more"), ("inference", "Dimza built a house")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_6_167 : LinguisticExample :=
  { id := "grubic2015_6_167"
    source := ⟨"grubic-2015", "(167)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Dimza ke salko bano."
    discourseSegments := []
    glossedTokens := [("Dimza", "Dimza"), ("ke", "also"), ("salko", "build.PFV"), ("bano.", "house")]
    translation := "Dimza also built a house."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "ke"), ("configuration", "unmarkedObjectFocus"), ("inference", "Dimza built a house"), ("inference", "Dimza built something else")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_6_168 : LinguisticExample :=
  { id := "grubic2015_6_168"
    source := ⟨"grubic-2015", "(168)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Dimza har salko bano."
    discourseSegments := []
    glossedTokens := [("Dimza", "Dimza"), ("har", "even"), ("salko", "build.PFV"), ("bano.", "house")]
    translation := "Dimza even built a house."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "har"), ("configuration", "unmarkedObjectFocus"), ("inference", "Dimza built a house"), ("inference", "he was expected to build less"), ("inference", "Dimza built something else")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_6_169 : LinguisticExample :=
  { id := "grubic2015_6_169"
    source := ⟨"grubic-2015", "(169)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Ne sakatari yak'i."
    discourseSegments := []
    glossedTokens := [("Ne", "1SG"), ("sakatari", "secretary"), ("yak'i.", "only")]
    translation := "I'm only a secretary."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "yak"), ("configuration", "predicate"), ("inference", "the speaker is nothing better than a secretary"), ("inference", "the speaker was expected to be something better")]
    comment := "A rank-order scale: the prejacent inference does not survive negation."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_6_170 : LinguisticExample :=
  { id := "grubic2015_6_170"
    source := ⟨"grubic-2015", "(170)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Bah malum har'i."
    discourseSegments := []
    glossedTokens := [("Bah", "Bah"), ("malum", "teacher"), ("har'i.", "even")]
    translation := "Bah is even a teacher."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "har"), ("configuration", "predicate"), ("inference", "Bah is a teacher"), ("inference", "he was expected to be something worse")]
    comment := "A rank-order scale: no additive inference."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_7_41 : LinguisticExample :=
  { id := "grubic2015_7_41"
    source := ⟨"grubic-2015", "(41)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Kaja mato=i Hawwa, salko bano=i ke Kule."
    discourseSegments := []
    glossedTokens := [("Kaja", "buy.PFV"), ("mato=i", "car=BM"), ("Hawwa,", "Hawwa"), ("salko", "build.PFV"), ("bano=i", "house=BM"), ("ke", "also"), ("Kule.", "Kule")]
    translation := "Hawwa bought a car, Kule built a house."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "ke"), ("configuration", "distinctBackgroundDistinctFocus")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_7_42 : LinguisticExample :=
  { id := "grubic2015_7_42"
    source := ⟨"grubic-2015", "(42)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Salko bano=i Kule, kaja mato=i ke Kule."
    discourseSegments := []
    glossedTokens := [("Salko", "build.PFV"), ("bano=i", "house=BM"), ("Kule,", "Kule"), ("kaja", "buy.PFV"), ("mato=i", "car=BM"), ("ke", "also"), ("Kule.", "Kule")]
    translation := "Kule built a house, and Kule also bought a car."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "ke"), ("configuration", "distinctBackgroundParallelFocus")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_7_43 : LinguisticExample :=
  { id := "grubic2015_7_43"
    source := ⟨"grubic-2015", "(43)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Kule salko makaranta mano, Kule ke salko bano mano."
    discourseSegments := []
    glossedTokens := [("Kule", "Kule"), ("salko", "build.PFV"), ("makaranta", "school"), ("mano,", "last.year"), ("Kule", "Kule"), ("ke", "also"), ("salko", "build.PFV"), ("bano", "house"), ("mano.", "last.year")]
    translation := "Kule built a school last year, and Kule also built a house last year."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "ke"), ("configuration", "parallelUnmarkedBackground")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_7_44 : LinguisticExample :=
  { id := "grubic2015_7_44"
    source := ⟨"grubic-2015", "(44)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Salko bano=i Hawwa, salko bano=i ke Kule."
    discourseSegments := []
    glossedTokens := [("Salko", "build.PFV"), ("bano=i", "house=BM"), ("Hawwa,", "Hawwa"), ("salko", "build.PFV"), ("bano=i", "house=BM"), ("ke", "also"), ("Kule.", "Kule")]
    translation := "Hawwa built a house, and Kule built a house, too."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "ke"), ("configuration", "parallelMarkedBackground")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_7_46 : LinguisticExample :=
  { id := "grubic2015_7_46"
    source := ⟨"grubic-2015", "(46)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Bei a ina ham ɗoshi, ke a ina ham tuha ke'e."
    discourseSegments := []
    glossedTokens := [("Bei", "maybe"), ("a", "3SG"), ("ina", "do.FUT"), ("ham", "water"), ("ɗoshi,", "tomorrow"), ("ke", "and"), ("a", "3SG"), ("ina", "do.FUT"), ("ham", "water"), ("tuha", "day.after.tomorrow"), ("ke'e.", "also")]
    translation := "It is possible that it will rain tomorrow, and it will also rain the day after tomorrow."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "ke"), ("configuration", "modalizedAntecedent")]
    comment := "The antecedent is merely given, not asserted to be true."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_7_48 : LinguisticExample :=
  { id := "grubic2015_7_48"
    source := ⟨"grubic-2015", "(48)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Salko bano=i Hawwa, Kule ke salko bano."
    discourseSegments := []
    glossedTokens := [("Salko", "build.PFV"), ("bano=i", "house=BM"), ("Hawwa,", "Hawwa"), ("Kule", "Kule"), ("ke", "also"), ("salko", "build.PFV"), ("bano.", "house")]
    translation := "Hawwa built a house and Kule also built a house."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("particle", "ke"), ("configuration", "nonParallel")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_7_49 : LinguisticExample :=
  { id := "grubic2015_7_49"
    source := ⟨"grubic-2015", "(49)"⟩
    reportedIn := none
    language := "ngam1282"
    primaryText := "Salko bano=i Hawwa, ke salko bano=i ke Kule."
    discourseSegments := []
    glossedTokens := [("Salko", "build.PFV"), ("bano=i", "house=BM"), ("Hawwa,", "Hawwa"), ("ke", "also"), ("salko", "build.PFV"), ("bano=i", "house=BM"), ("ke", "also"), ("Kule.", "Kule")]
    translation := "Hawwa built a house, and Kule also built a house."
    context := ""
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("particle", "ke"), ("configuration", "parallelMarkedBackground")]
    comment := "Possible if a temporal shift is accommodated: it is Hawwa that built the house and then Kule built a house."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex_6_24, ex_6_25a, ex_6_25b, ex_6_25c, ex_6_26, ex_6_28, ex_6_140, ex_6_145a, ex_6_145b, ex_6_148a, ex_6_148b, ex_6_149, ex_6_150a, ex_6_150b, ex_6_151, ex_6_153, ex_6_158, ex_6_159, ex_6_160, ex_6_162a, ex_6_162b, ex_6_163, ex_6_164, ex_6_165, ex_6_166, ex_6_167, ex_6_168, ex_6_169, ex_6_170, ex_7_41, ex_7_42, ex_7_43, ex_7_44, ex_7_46, ex_7_48, ex_7_49]

end Grubic2015.Examples
