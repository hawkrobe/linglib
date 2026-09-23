module

public import Linglib.Data.Examples.Schema

/-!
# `Matthewson2013` — typed example data

Auto-generated from `Linglib/Data/Examples/Matthewson2013.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Matthewson2013.Examples`.
-/

@[expose] public section

namespace Matthewson2013.Examples

open Data.Examples

def ex22 : LinguisticExample :=
  { id := "matthewson2013_ex22"
    source := ⟨"matthewson-2013", "(22)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa/ima'=hl wis"
    discourseSegments := []
    glossedTokens := [("yugw=imaa/ima'=hl", "IPFV=EPIS=CN"), ("wis", "rain")]
    translation := "It might be raining."
    context := "You hear pattering, and you're not entirely sure what it is."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "present"), ("prospective", "false"), ("figure", "4")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex29 : LinguisticExample :=
  { id := "matthewson2013_ex29"
    source := ⟨"matthewson-2013", "(29)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa=hl siipxw-t"
    discourseSegments := []
    glossedTokens := [("yugw=imaa=hl", "IPFV=EPIS=CN"), ("siipxw-t", "sick-3SG.II")]
    translation := "He must have been sick."
    context := "Joe left the meeting looking really green in the face and sweaty. Someone asks you why he left."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "past"), ("prospective", "false"), ("figure", "4"), ("force", "strong")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex30 : LinguisticExample :=
  { id := "matthewson2013_ex30"
    source := ⟨"matthewson-2013", "(30)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa=hl da'awhl ixwt oo ligi nee=yimaa=dii ixwt"
    discourseSegments := []
    glossedTokens := [("yugw=imaa=hl", "IPFV=EPIS=CN"), ("da'awhl", "then"), ("ixwt", "fish"), ("oo", "or"), ("ligi", "INDEF"), ("nee=yimaa=dii", "NEG=EPIS=CNTR"), ("ixwt", "fish")]
    translation := "Maybe he's fishing, maybe he's not fishing."
    context := "You thought your friend was fishing. But you see his rod and tackle box are still at his house. You really don't know if he's fishing or not."
    judgment := .acceptable
    alternatives := []
    readings := [("possibly not", .acceptable)]
    paperFeatures := [("section", "3.1"), ("modal", "ima('a)"), ("negated", "true")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex37 : LinguisticExample :=
  { id := "matthewson2013_ex37"
    source := ⟨"matthewson-2013", "(37)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa=hl xsdaa-diit"
    discourseSegments := []
    glossedTokens := [("yugw=imaa=hl", "IPFV=EPIS=CN"), ("xsdaa-diit", "win-3PL.II")]
    translation := "They might have been winning. [according to my evidence last night]"
    context := "The Canucks were playing last night. You weren't watching the game but you heard your son sounding excited and happy from the living room where he was watching the game, so you thought they were winning. You found out after the game that the Canucks lost 20–0, and your son was happy about something else that his friend had told him on his cellphone."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "past"), ("orientation", "present"), ("prospective", "false"), ("figure", "4")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex38a : LinguisticExample :=
  { id := "matthewson2013_ex38a"
    source := ⟨"matthewson-2013", "(38a)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa=hl xsdaa-diit"
    discourseSegments := []
    glossedTokens := [("yugw=imaa=hl", "IPFV=EPIS=CN"), ("xsdaa-diit", "win-3PL.II")]
    translation := "They might be winning."
    context := "You can hear people hollering, so the Canucks might be winning."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "present"), ("prospective", "false")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex38b : LinguisticExample :=
  { id := "matthewson2013_ex38b"
    source := ⟨"matthewson-2013", "(38b)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa[=hl] dim xsdaa-diit"
    discourseSegments := []
    glossedTokens := [("yugw=imaa[=hl]", "IPFV=EPIS[=CN]"), ("dim", "FUT"), ("xsdaa-diit", "win-3PL.II")]
    translation := "They might win."
    context := "You are watching the Canucks. They might win."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "future"), ("prospective", "true")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex39a : LinguisticExample :=
  { id := "matthewson2013_ex39a"
    source := ⟨"matthewson-2013", "(39a)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa/ima'=hl wis"
    discourseSegments := []
    glossedTokens := [("yugw=imaa/ima'=hl", "IPFV=EPIS=CN"), ("wis", "rain")]
    translation := "It might have rained. / It might be raining."
    context := "You see puddles, and the flowers looking fresh and damp."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "past"), ("prospective", "false")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex40a : LinguisticExample :=
  { id := "matthewson2013_ex40a"
    source := ⟨"matthewson-2013", "(40a)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa/ima'=hl dim wis"
    discourseSegments := []
    glossedTokens := [("yugw=imaa/ima'=hl", "IPFV=EPIS=CN"), ("dim", "FUT"), ("wis", "rain")]
    translation := "It might rain (in the future)."
    context := "You see puddles, and the flowers looking fresh and damp."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "past"), ("prospective", "true")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex41a : LinguisticExample :=
  { id := "matthewson2013_ex41a"
    source := ⟨"matthewson-2013", "(41a)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa/ima'=hl siipxw-t"
    discourseSegments := []
    glossedTokens := [("yugw=imaa/ima'=hl", "IPFV=EPIS=CN"), ("siipxw-t", "sick-3SG.II")]
    translation := "He might have been sick. / He might be sick (now)."
    context := "Why wasn't Joe at the meeting yesterday?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "past"), ("prospective", "false")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex42a : LinguisticExample :=
  { id := "matthewson2013_ex42a"
    source := ⟨"matthewson-2013", "(42a)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa/ima'=hl dim siipxw-t"
    discourseSegments := []
    glossedTokens := [("yugw=imaa/ima'=hl", "IPFV=EPIS=CN"), ("dim", "FUT"), ("siipxw-t", "sick-3SG.II")]
    translation := "He might be sick (in future)."
    context := "Why wasn't Joe at the meeting yesterday?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "past"), ("prospective", "true")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex39b : LinguisticExample :=
  { id := "matthewson2013_ex39b"
    source := ⟨"matthewson-2013", "(39b)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa/ima'=hl wis"
    discourseSegments := []
    glossedTokens := [("yugw=imaa/ima'=hl", "IPFV=EPIS=CN"), ("wis", "rain")]
    translation := "It might have rained. / It might be raining."
    context := "You hear pattering on the roof."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "present"), ("prospective", "false")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex40b : LinguisticExample :=
  { id := "matthewson2013_ex40b"
    source := ⟨"matthewson-2013", "(40b)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa/ima'=hl dim wis"
    discourseSegments := []
    glossedTokens := [("yugw=imaa/ima'=hl", "IPFV=EPIS=CN"), ("dim", "FUT"), ("wis", "rain")]
    translation := "It might rain (in the future)."
    context := "You hear pattering on the roof."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "present"), ("prospective", "true")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex41b : LinguisticExample :=
  { id := "matthewson2013_ex41b"
    source := ⟨"matthewson-2013", "(41b)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa/ima'=hl siipxw-t"
    discourseSegments := []
    glossedTokens := [("yugw=imaa/ima'=hl", "IPFV=EPIS=CN"), ("siipxw-t", "sick-3SG.II")]
    translation := "He might have been sick. / He might be sick (now)."
    context := "Why isn't Joe here?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "present"), ("prospective", "false")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex42b : LinguisticExample :=
  { id := "matthewson2013_ex42b"
    source := ⟨"matthewson-2013", "(42b)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa/ima'=hl dim siipxw-t"
    discourseSegments := []
    glossedTokens := [("yugw=imaa/ima'=hl", "IPFV=EPIS=CN"), ("dim", "FUT"), ("siipxw-t", "sick-3SG.II")]
    translation := "He might be sick (in future)."
    context := "Why isn't Joe here?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "present"), ("prospective", "true")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex39c : LinguisticExample :=
  { id := "matthewson2013_ex39c"
    source := ⟨"matthewson-2013", "(39c)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa/ima'=hl wis"
    discourseSegments := []
    glossedTokens := [("yugw=imaa/ima'=hl", "IPFV=EPIS=CN"), ("wis", "rain")]
    translation := "It might have rained. / It might be raining."
    context := "You hear thunder, so you think it might rain soon."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "future"), ("prospective", "false")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex40c : LinguisticExample :=
  { id := "matthewson2013_ex40c"
    source := ⟨"matthewson-2013", "(40c)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa/ima'=hl dim wis"
    discourseSegments := []
    glossedTokens := [("yugw=imaa/ima'=hl", "IPFV=EPIS=CN"), ("dim", "FUT"), ("wis", "rain")]
    translation := "It might rain (in the future)."
    context := "You hear thunder, so you think it might rain soon."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "future"), ("prospective", "true")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex41c : LinguisticExample :=
  { id := "matthewson2013_ex41c"
    source := ⟨"matthewson-2013", "(41c)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa/ima'=hl siipxw-t"
    discourseSegments := []
    glossedTokens := [("yugw=imaa/ima'=hl", "IPFV=EPIS=CN"), ("siipxw-t", "sick-3SG.II")]
    translation := "He might have been sick. / He might be sick (now)."
    context := "He's wearing no coat in the rain, he might get sick."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "future"), ("prospective", "false")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex42c : LinguisticExample :=
  { id := "matthewson2013_ex42c"
    source := ⟨"matthewson-2013", "(42c)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa/ima'=hl dim siipxw-t"
    discourseSegments := []
    glossedTokens := [("yugw=imaa/ima'=hl", "IPFV=EPIS=CN"), ("dim", "FUT"), ("siipxw-t", "sick-3SG.II")]
    translation := "He might be sick (in future)."
    context := "He's wearing no coat in the rain, he might get sick."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "present"), ("orientation", "future"), ("prospective", "true")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex43a : LinguisticExample :=
  { id := "matthewson2013_ex43a"
    source := ⟨"matthewson-2013", "(43a)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa=hl wis da'awhl"
    discourseSegments := []
    glossedTokens := [("yugw=imaa=hl", "IPFV=EPIS=CN"), ("wis", "rain"), ("da'awhl", "then")]
    translation := "It might have rained. [based on my evidence earlier]"
    context := "When you looked out your window earlier today, the ground was wet, so it looked like it might have rained. But you found out later that the sprinklers had been watering the ground."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "past"), ("orientation", "past"), ("prospective", "false"), ("figure", "4")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex43a' : LinguisticExample :=
  { id := "matthewson2013_ex43a'"
    source := ⟨"matthewson-2013", "(43a')"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa=hl dim wis da'awhl"
    discourseSegments := []
    glossedTokens := [("yugw=imaa=hl", "IPFV=EPIS=CN"), ("dim", "FUT"), ("wis", "rain"), ("da'awhl", "then")]
    translation := "It might have rained. [based on my evidence earlier]"
    context := "When you looked out your window earlier today, the ground was wet, so it looked like it might have rained. But you found out later that the sprinklers had been watering the ground."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "past"), ("orientation", "past"), ("prospective", "true")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex44 : LinguisticExample :=
  { id := "matthewson2013_ex44"
    source := ⟨"matthewson-2013", "(44)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa=hl dim wis"
    discourseSegments := []
    glossedTokens := [("yugw=imaa=hl", "IPFV=EPIS=CN"), ("dim", "FUT"), ("wis", "rain")]
    translation := "It might have been going to rain."
    context := "This morning you looked out your window and judging by the clouds, it looked like it might have been going to rain, so you took your raincoat. Later you're explaining to me why you did that."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "past"), ("orientation", "future"), ("prospective", "true"), ("figure", "4")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex44' : LinguisticExample :=
  { id := "matthewson2013_ex44'"
    source := ⟨"matthewson-2013", "(44')"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa=hl wis"
    discourseSegments := []
    glossedTokens := [("yugw=imaa=hl", "IPFV=EPIS=CN"), ("wis", "rain")]
    translation := "It might have been going to rain."
    context := "This morning you looked out your window and judging by the clouds, it looked like it might have been going to rain, so you took your raincoat. Later you're explaining to me why you did that."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "ima('a)"), ("perspective", "past"), ("orientation", "future"), ("prospective", "false")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex47a : LinguisticExample :=
  { id := "matthewson2013_ex47a"
    source := ⟨"matthewson-2013", "(47a)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "limx=gat[=t] Bob"
    discourseSegments := []
    glossedTokens := [("limx=gat[=t]", "sing=REPORT[=DM]"), ("Bob", "Bob")]
    translation := "(I heard that) Bob sang."
    context := "Yesterday, Henry told you that Bob sang last week."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "gat"), ("perspective", "past"), ("orientation", "past"), ("prospective", "false"), ("figure", "4")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex48a : LinguisticExample :=
  { id := "matthewson2013_ex48a"
    source := ⟨"matthewson-2013", "(48a)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "dim limx=gat[=t] Bob"
    discourseSegments := []
    glossedTokens := [("dim", "FUT"), ("limx=gat[=t]", "sing=REPORT[=DM]"), ("Bob", "Bob")]
    translation := "(I heard that) Bob would/will sing."
    context := "Yesterday, Henry told you that Bob sang last week."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "gat"), ("perspective", "past"), ("orientation", "past"), ("prospective", "true")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex47b : LinguisticExample :=
  { id := "matthewson2013_ex47b"
    source := ⟨"matthewson-2013", "(47b)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "limx=gat[=t] Bob"
    discourseSegments := []
    glossedTokens := [("limx=gat[=t]", "sing=REPORT[=DM]"), ("Bob", "Bob")]
    translation := "(I heard that) Bob sang."
    context := "Yesterday, Henry told you that Bob was singing (at that time)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "gat"), ("perspective", "past"), ("orientation", "present"), ("prospective", "false"), ("figure", "4")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex48b : LinguisticExample :=
  { id := "matthewson2013_ex48b"
    source := ⟨"matthewson-2013", "(48b)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "dim limx=gat[=t] Bob"
    discourseSegments := []
    glossedTokens := [("dim", "FUT"), ("limx=gat[=t]", "sing=REPORT[=DM]"), ("Bob", "Bob")]
    translation := "(I heard that) Bob would/will sing."
    context := "Yesterday, Henry told you that Bob was singing (at that time)."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "gat"), ("perspective", "past"), ("orientation", "present"), ("prospective", "true")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex47c : LinguisticExample :=
  { id := "matthewson2013_ex47c"
    source := ⟨"matthewson-2013", "(47c)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "limx=gat[=t] Bob"
    discourseSegments := []
    glossedTokens := [("limx=gat[=t]", "sing=REPORT[=DM]"), ("Bob", "Bob")]
    translation := "(I heard that) Bob sang."
    context := "Yesterday, Henry told you that Bob would be singing later that day."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "gat"), ("perspective", "past"), ("orientation", "future"), ("prospective", "false")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex48c : LinguisticExample :=
  { id := "matthewson2013_ex48c"
    source := ⟨"matthewson-2013", "(48c)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "dim limx=gat[=t] Bob"
    discourseSegments := []
    glossedTokens := [("dim", "FUT"), ("limx=gat[=t]", "sing=REPORT[=DM]"), ("Bob", "Bob")]
    translation := "(I heard that) Bob would/will sing."
    context := "Yesterday, Henry told you that Bob would be singing later that day."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.3"), ("modal", "gat"), ("perspective", "past"), ("orientation", "future"), ("prospective", "true"), ("figure", "4")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex53 : LinguisticExample :=
  { id := "matthewson2013_ex53"
    source := ⟨"matthewson-2013", "(53)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "da'akxw-i=hl t'xalpx-a gat dim luu wan-diit goo=hl ts'im kyaa tust"
    discourseSegments := []
    glossedTokens := [("da'akxw-i=hl", "CIRC.POSS-TRA=CN"), ("t'xalpx-a", "four-LINK"), ("gat", "people"), ("dim", "FUT"), ("luu", "in"), ("wan-diit", "sit-3PL.II"), ("goo=hl", "LOC=CN"), ("ts'im", "inside"), ("kyaa", "car"), ("tust", "that")]
    translation := "Four people can fit in this car."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("modal", "da'akhlxw"), ("orientation", "present"), ("prospective", "true")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex53' : LinguisticExample :=
  { id := "matthewson2013_ex53'"
    source := ⟨"matthewson-2013", "(53')"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "da'akxw-i=hl t'xalpx-a gat luu wan-diit goo=hl ts'im kyaa tust"
    discourseSegments := []
    glossedTokens := [("da'akxw-i=hl", "CIRC.POSS-TRA=CN"), ("t'xalpx-a", "four-LINK"), ("gat", "people"), ("luu", "in"), ("wan-diit", "sit-3PL.II"), ("goo=hl", "LOC=CN"), ("ts'im", "inside"), ("kyaa", "car"), ("tust", "that")]
    translation := "Four people can fit in this car."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("modal", "da'akhlxw"), ("orientation", "present"), ("prospective", "false")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex56 : LinguisticExample :=
  { id := "matthewson2013_ex56"
    source := ⟨"matthewson-2013", "(56)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "da'akhlxw-i-'y dim hahla'lsd-i'y k'yoots"
    discourseSegments := []
    glossedTokens := [("da'akhlxw-i-'y", "CIRC.POSS-TRA-1SG.II"), ("dim", "FUT"), ("hahla'lsd-i'y", "work-1SG.II"), ("k'yoots", "yesterday")]
    translation := "I was able to work yesterday."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("modal", "da'akhlxw"), ("orientation", "past"), ("prospective", "true")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex56' : LinguisticExample :=
  { id := "matthewson2013_ex56'"
    source := ⟨"matthewson-2013", "(56')"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "da'akhlxw-i-'y hahla'lsd-i'y k'yoots"
    discourseSegments := []
    glossedTokens := [("da'akhlxw-i-'y", "CIRC.POSS-TRA-1SG.II"), ("hahla'lsd-i'y", "work-1SG.II"), ("k'yoots", "yesterday")]
    translation := "I was able to work yesterday."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("modal", "da'akhlxw"), ("orientation", "past"), ("prospective", "false")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex62 : LinguisticExample :=
  { id := "matthewson2013_ex62"
    source := ⟨"matthewson-2013", "(62)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "da'akhlxw-i-'y dim hahla'lsd-i'y k'yoots, ii ap nee=dii wil-'y"
    discourseSegments := []
    glossedTokens := [("da'akhlxw-i-'y", "CIRC.POSS-TRA-1SG.II"), ("dim", "FUT"), ("hahla'lsd-i'y", "work-1SG.II"), ("k'yoots", "yesterday"), ("ii", "and"), ("ap", "EMPH"), ("nee=dii", "NEG=CONT"), ("wil-'y", "COMP-1SG.II")]
    translation := "I was able to work yesterday, but I didn't."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.1"), ("modal", "da'akhlxw"), ("orientation", "past"), ("prospective", "true"), ("actualityEntailment", "false")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex73 : LinguisticExample :=
  { id := "matthewson2013_ex73"
    source := ⟨"matthewson-2013", "(73)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "anook-xw(=hl) dim ha'w-s Savanna k'yoots"
    discourseSegments := []
    glossedTokens := [("anook-xw(=hl)", "DEON.POSS-MED(=CN)"), ("dim", "FUT"), ("ha'w-s", "go.home-PN"), ("Savanna", "Savanna"), ("k'yoots", "yesterday")]
    translation := "It was allowed that Savanna went home."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "anook(xw)"), ("orientation", "past"), ("prospective", "true")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex73' : LinguisticExample :=
  { id := "matthewson2013_ex73'"
    source := ⟨"matthewson-2013", "(73')"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "anook-xw(=hl) ha'w-s Savanna k'yoots"
    discourseSegments := []
    glossedTokens := [("anook-xw(=hl)", "DEON.POSS-MED(=CN)"), ("ha'w-s", "go.home-PN"), ("Savanna", "Savanna"), ("k'yoots", "yesterday")]
    translation := "It was allowed that Savanna went home."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "anook(xw)"), ("orientation", "past"), ("prospective", "false")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex83 : LinguisticExample :=
  { id := "matthewson2013_ex83"
    source := ⟨"matthewson-2013", "(83)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "sgi dim ap ha'w-s Lisa"
    discourseSegments := []
    glossedTokens := [("sgi", "CIRC.NECESS"), ("dim", "FUT"), ("ap", "EMPH"), ("ha'w-s", "go.home-PN"), ("Lisa", "Lisa")]
    translation := "Lisa should/must go home."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("modal", "sgi"), ("orientation", "present"), ("prospective", "true")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex83' : LinguisticExample :=
  { id := "matthewson2013_ex83'"
    source := ⟨"matthewson-2013", "(83')"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "sgi ap ha'w-s Lisa"
    discourseSegments := []
    glossedTokens := [("sgi", "CIRC.NECESS"), ("ap", "EMPH"), ("ha'w-s", "go.home-PN"), ("Lisa", "Lisa")]
    translation := "Lisa should/must go home."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("modal", "sgi"), ("orientation", "present"), ("prospective", "false")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex95a : LinguisticExample :=
  { id := "matthewson2013_ex95a"
    source := ⟨"matthewson-2013", "(95a)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "dim hadiswa-'y"
    discourseSegments := []
    glossedTokens := [("dim", "FUT"), ("hadiswa-'y", "sneeze-1SG.II")]
    translation := "I have to sneeze. [Lit., I'm going to sneeze.]"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("test", "sneeze"), ("modal", "dim")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex96 : LinguisticExample :=
  { id := "matthewson2013_ex96"
    source := ⟨"matthewson-2013", "(96)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "sgi dim hajiswa-'y"
    discourseSegments := []
    glossedTokens := [("sgi", "CIRC.NECESS"), ("dim", "FUT"), ("hajiswa-'y", "sneeze-1SG.II")]
    translation := "I should sneeze."
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.3"), ("test", "sneeze"), ("modal", "sgi")]
    comment := "Rejected in context by one consultant, marginally accepted by the other."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex22, ex29, ex30, ex37, ex38a, ex38b, ex39a, ex40a, ex41a, ex42a, ex39b, ex40b, ex41b, ex42b, ex39c, ex40c, ex41c, ex42c, ex43a, ex43a', ex44, ex44', ex47a, ex48a, ex47b, ex48b, ex47c, ex48c, ex53, ex53', ex56, ex56', ex62, ex73, ex73', ex83, ex83', ex95a, ex96]

end Matthewson2013.Examples
