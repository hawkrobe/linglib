module

public import Linglib.Data.Examples.Schema

/-!
# `Toosarvandani2023` — typed example data

Auto-generated from `Linglib/Data/Examples/Toosarvandani2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Toosarvandani2023.Examples`.
-/

@[expose] public section

namespace Toosarvandani2023.Examples

open Data.Examples

def ex_16a : LinguisticExample :=
  { id := "toosarvandani2023_16a"
    source := ⟨"toosarvandani-2023", "(16a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We are (both) behind the gift shop."
    discourseSegments := []
    glossedTokens := []
    translation := "We are (both) behind the gift shop."
    context := "Paul is alone at the zoo, at the lion's cage; Josie, who has never been to the zoo, calls him: 'I saw you in a picture with the lion. Where are you?'"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "1pl"), ("group", "speaker and lion"), ("property", "context-dependence")]
    comment := "The speaker and the lion are not associates in the context, so the first-person plural cannot refer to the group, though (16b) *they* can."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_16b : LinguisticExample :=
  { id := "toosarvandani2023_16b"
    source := ⟨"toosarvandani-2023", "(16b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "They are (both) behind the gift shop."
    discourseSegments := []
    glossedTokens := []
    translation := "They are (both) behind the gift shop."
    context := "Josie asks a zoo ranger: 'I saw my friend in a picture with the lion. Where are they?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "3pl"), ("group", "Paul and lion"), ("property", "context-dependence")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_17a : LinguisticExample :=
  { id := "toosarvandani2023_17a"
    source := ⟨"toosarvandani-2023", "(17a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We are (both) behind the oak tree."
    discourseSegments := []
    glossedTokens := []
    translation := "We are (both) behind the oak tree."
    context := "Sam is at the dog park with his beloved Doberman Franz; Leslie calls: 'Are you here with Franz? Where are you?'"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "1pl"), ("group", "speaker and pet dog"), ("property", "context-dependence")]
    comment := "A beloved pet counts as an associate, so the mixed human-animal group takes *we*."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_18a : LinguisticExample :=
  { id := "toosarvandani2023_18a"
    source := ⟨"toosarvandani-2023", "(18a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We are (both) in the field at the edge of town."
    discourseSegments := []
    glossedTokens := []
    translation := "We are (both) in the field at the edge of town."
    context := "Maria, a skydiver blown off course, calls the company; the receptionist says: 'We will come pick you up. We will also pick up your parachute at the same time. Where are you?'"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("pronoun", "1pl"), ("group", "speaker and parachute"), ("property", "context-dependence")]
    comment := "A first-person plural cannot refer to the speaker and an inanimate object; (18b) *they* can."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_77a : LinguisticExample :=
  { id := "toosarvandani2023_77a"
    source := ⟨"toosarvandani-2023", "(77a)"⟩
    reportedIn := none
    language := "yala1267"
    primaryText := "Bet=gak=a'=ba'."
    discourseSegments := []
    glossedTokens := []
    translation := "I killed [them]."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "1sg"), ("object", "3.an"), ("configuration", "1 > 3"), ("cliticization", "both")]
    comment := "kill.comp=pl=1sg=3.an; Yalálag, from Avelino Becerra (2004). A first-person subject clitic with a third-person animal object clitic."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_77b : LinguisticExample :=
  { id := "toosarvandani2023_77b"
    source := ⟨"toosarvandani-2023", "(77b)"⟩
    reportedIn := none
    language := "yala1267"
    primaryText := "Bnaw=ba'=a'."
    discourseSegments := []
    glossedTokens := []
    translation := "It followed me."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3.an"), ("object", "1sg"), ("configuration", "3 > 1"), ("cliticization", "object blocked")]
    comment := "follow.comp=3.an=1sg; the person-case constraint: a local-person object cannot cliticize under a third-person subject."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_78a : LinguisticExample :=
  { id := "toosarvandani2023_78a"
    source := ⟨"toosarvandani-2023", "(78a)"⟩
    reportedIn := none
    language := "yala1267"
    primaryText := "Bet=te=o'=ba'."
    discourseSegments := []
    glossedTokens := []
    translation := "You killed [it]."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "2sg"), ("object", "3.an"), ("configuration", "2 > 3"), ("cliticization", "both")]
    comment := "kill.comp=adv=2sg=3.an."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_78b : LinguisticExample :=
  { id := "toosarvandani2023_78b"
    source := ⟨"toosarvandani-2023", "(78b)"⟩
    reportedIn := none
    language := "yala1267"
    primaryText := "Bet=te=ba'=o'."
    discourseSegments := []
    glossedTokens := []
    translation := "[It] killed you."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3.an"), ("object", "2sg"), ("configuration", "3 > 2"), ("cliticization", "object blocked")]
    comment := "kill.comp=adv=3.an=2sg."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_79a : LinguisticExample :=
  { id := "toosarvandani2023_79a"
    source := ⟨"toosarvandani-2023", "(79a)"⟩
    reportedIn := none
    language := "yala1267"
    primaryText := "Wkwell=e'=be'."
    discourseSegments := []
    glossedTokens := []
    translation := "S/he (an elder) made her/him (a nonelder) cry."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3.el"), ("object", "3.hu"), ("configuration", "3.el > 3.hu"), ("cliticization", "both")]
    comment := "make.cry.comp=3.el=3.hu; the animacy-based constraint of Foley and Toosarvandani: the subject outranks the object in animacy."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_79b : LinguisticExample :=
  { id := "toosarvandani2023_79b"
    source := ⟨"toosarvandani-2023", "(79b)"⟩
    reportedIn := none
    language := "yala1267"
    primaryText := "Wkwell=be'=e'."
    discourseSegments := []
    glossedTokens := []
    translation := "S/he (a nonelder) made her/him (an elder) cry."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3.hu"), ("object", "3.el"), ("configuration", "3.hu > 3.el"), ("cliticization", "object blocked")]
    comment := "make.cry.comp=3.hu=3.el; in the Laxopa variety, whose probe does not see the elder feature, this combination is permitted."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_80a : LinguisticExample :=
  { id := "toosarvandani2023_80a"
    source := ⟨"toosarvandani-2023", "(80a)"⟩
    reportedIn := none
    language := "yala1267"
    primaryText := "Bchew=be'=ba'."
    discourseSegments := []
    glossedTokens := []
    translation := "S/he kicked it (an animal)."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3.hu"), ("object", "3.an"), ("configuration", "3.hu > 3.an"), ("cliticization", "both")]
    comment := "kick.comp=3.hu=3.an."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_80b : LinguisticExample :=
  { id := "toosarvandani2023_80b"
    source := ⟨"toosarvandani-2023", "(80b)"⟩
    reportedIn := none
    language := "yala1267"
    primaryText := "Bdinn=ba'=be'."
    discourseSegments := []
    glossedTokens := []
    translation := "It (an animal) bit her/him."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3.an"), ("object", "3.hu"), ("configuration", "3.an > 3.hu"), ("cliticization", "object blocked")]
    comment := "bite.comp=3.an=3.hu."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_81a : LinguisticExample :=
  { id := "toosarvandani2023_81a"
    source := ⟨"toosarvandani-2023", "(81a)"⟩
    reportedIn := none
    language := "yala1267"
    primaryText := "Bchochj=ba'=n."
    discourseSegments := []
    glossedTokens := []
    translation := "It (an animal) hit it."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3.an"), ("object", "3.in"), ("configuration", "3.an > 3.in"), ("cliticization", "both")]
    comment := "hit.comp=3.an=3.in."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_81b : LinguisticExample :=
  { id := "toosarvandani2023_81b"
    source := ⟨"toosarvandani-2023", "(81b)"⟩
    reportedIn := none
    language := "yala1267"
    primaryText := "Bchochj=en=ba'."
    discourseSegments := []
    glossedTokens := []
    translation := "It hit it (an animal)."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("subject", "3.in"), ("object", "3.an"), ("configuration", "3.in > 3.an"), ("cliticization", "object blocked")]
    comment := "hit.comp=3.in=3.an; in the Zoogocho variety, whose probe sees only the animate feature, any combination of animate clitics is allowed."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_16a, ex_16b, ex_17a, ex_18a, ex_77a, ex_77b, ex_78a, ex_78b, ex_79a, ex_79b, ex_80a, ex_80b, ex_81a, ex_81b]

end Toosarvandani2023.Examples
