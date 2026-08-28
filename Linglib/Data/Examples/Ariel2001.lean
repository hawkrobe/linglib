import Linglib.Data.Examples.Schema

/-!
# `Ariel2001` — typed example data

Auto-generated from `Linglib/Data/Examples/Ariel2001.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Ariel2001.Examples`.
-/

namespace Ariel2001.Examples

open Data.Examples

def ex_1 : LinguisticExample :=
  { id := "ariel2001_1"
    source := ⟨"ariel-2001", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Melissa: Well, I'll say awakened, cause that's what I have written. Ron: (Sniff). Frank: Just watch, He'll put a note by it – note by that. I really like that word Melissa."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "proxDem"), ("marker", "unstressedPron"), ("marker", "distalDem"), ("marker", "distalDemNP")]
    comment := "Household corpus. The word awakened is referred to by that, it, that, and that word."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3 : LinguisticExample :=
  { id := "ariel2001_3"
    source := ⟨"ariel-2001", "(3)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "In the complaint the woman claimed that on May 2, ∅ met Roter … Then the two demanded from her to have sex with them. According to her, when ∅ refused, Roter started punching her …"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("source", "Haaretz"), ("perspective", "victim"), ("victim", "zero"), ("rapists", "lastName")]
    comment := "Haaretz, 17 May 1995; the paper prints its English rendering. In the second sentence the victim is coded by zero and the rapist by a proper name."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4 : LinguisticExample :=
  { id := "ariel2001_4"
    source := ⟨"ariel-2001", "(4)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "According to the police, Roter and the rape victim met in the beginning of May … and at a certain point ∅ asked the rape victim to have sex with them. This one refused, and as a result, the two cruelly raped her …"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("source", "Maariv"), ("perspective", "rapists"), ("victim", "proxDem"), ("rapists", "zero")]
    comment := "Maariv, 17 May 1995; the paper prints its English rendering. In the second sentence the rapists are coded by zero and the victim by a demonstrative pronoun."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5 : LinguisticExample :=
  { id := "ariel2001_5"
    source := ⟨"ariel-2001", "(5)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "But I insisted then. A person devoted two months and a half, ∅ built a whole program, ∅ took care of a budget, it is not as if Minister Katzav gave me, I took care, I went …"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("speaker", "self")]
    comment := "Mudai, TV interview, 2 November 1998 (Mulokandov and Rieder 1998). The speaker refers to himself by first-person forms and by third-person generic forms."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6 : LinguisticExample :=
  { id := "ariel2001_6"
    source := ⟨"ariel-2001", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "In the garden, I saw a young girl kicking a tree. I looked at them for a while."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("antecedent", "girl and tree"), ("marker", "unstressedPron")]
    comment := "Sanford and Moxey's example: the second sentence is marked ? although both entities are highly accessible."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7 : LinguisticExample :=
  { id := "ariel2001_7"
    source := ⟨"ariel-2001", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Morris: We broke a STRING, Or HE broke a string"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "stressedPron")]
    comment := "TV interview with Yo Yo Ma and Mark Morris, Israeli TV, 9 July 1998."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8a : LinguisticExample :=
  { id := "ariel2001_8a"
    source := ⟨"ariel-2001", "(8a)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "Arafat invited Kadafi to pray in Jerusalem, when it will be the Palestinian capital"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "headline"), ("marker", "lastName"), ("marker", "lastName"), ("marker", "fullName"), ("marker", "unstressedPron")]
    comment := "Haaretz, 14 July 1998, headline; the paper prints its English rendering. Markers in order: Arafat, Kadafi, Jerusalem, it."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8b : LinguisticExample :=
  { id := "ariel2001_8b"
    source := ⟨"ariel-2001", "(8b)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "The Palestinian authority chair, Yassir Arafat, invited the Lybian leader, Muamar Kadafi, to pray in Eastern Jerusalem, when this one will become the capital of the Palestinian state"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "opening sentence"), ("marker", "fullNameMod"), ("marker", "fullNameMod"), ("marker", "fullNameMod"), ("marker", "proxDem")]
    comment := "Haaretz, 14 July 1998, opening sentence; the paper prints its English rendering. Markers in order, matching (8a)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_9 : LinguisticExample :=
  { id := "ariel2001_9"
    source := ⟨"ariel-2001", "(9)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Frankly, I'm torn my own self as to which way to raise hell"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("marker", "stressedPron")]
    comment := "Clark Reed, quoted in The International Herald Tribune, 2–3 January 1999: a pronoun lengthened by self."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10 : LinguisticExample :=
  { id := "ariel2001_10"
    source := ⟨"ariel-2001", "(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "REBECCA: put the newspaper on his lap, RICKIE: Yeah, REBECCA: masturbated, and then lifted the paper up, RICKIE: Yeah, REBECCA: for her to see"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("the paper coreferent with the newspaper", .acceptable)]
    paperFeatures := [("marker", "shortDefDescription"), ("marker", "shortDefDescription")]
    comment := "Jury corpus. The shorter description the paper resumes the newspaper; no disjoint reading arises."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_12 : LinguisticExample :=
  { id := "ariel2001_12"
    source := ⟨"ariel-2001", "(12)"⟩
    reportedIn := none
    language := "hebr1245"
    primaryText := "It is not as if he looks like a hippie really, or anything like that. … Feil's grey-brown hair … covers his collar from behind. But one day in 93' the officer in charge of him demanded from him to have a haircut … The officer accused him …"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("topicMarker", "unstressedPron"), ("subjectMarker", "shortDefDescription")]
    comment := "Haaretz, 21 January 1999; the paper prints its English rendering. The discourse topic (officer Feil) is pronominal although the higher officer is the subject of two consecutive clauses."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def maya_rachel : LinguisticExample :=
  { id := "ariel2001_maya_rachel"
    source := ⟨"ariel-2001", "§1.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Maya kissed Rachel. And then she/SHE …"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("she = Maya", .acceptable), ("SHE = Rachel", .acceptable)]
    paperFeatures := [("maya", "unstressedPron"), ("rachel", "stressedPron")]
    comment := "The first-mentioned, topical but more distant Maya is later coded by an unstressed pronoun; the more recent, non-topical Rachel by a stressed pronoun."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8a, ex_8b, ex_9, ex_10, ex_12, maya_rachel]

end Ariel2001.Examples
