import Linglib.Data.Examples.Schema

/-!
# `Glass2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Glass2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Glass2025.Examples`.
-/

namespace Glass2025.Examples

open Data.Examples

def ex_1a : LinguisticExample :=
  { id := "glass2025_1a"
    source := ⟨"glass-2025", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex knows there's a meeting."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "There is a meeting."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "know"), ("state", "p")]
    comment := "The inference that there is a meeting projects through questions and negation, (1b)–(1c)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2a_p : LinguisticExample :=
  { id := "glass2025_2a_p"
    source := ⟨"glass-2025", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex thinks there's a meeting."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "There is a meeting."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "think"), ("state", "p")]
    comment := "Whether there is a meeting depends on Alex's trustworthiness and the plausibility of a meeting."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2a_unsettled : LinguisticExample :=
  { id := "glass2025_2a_unsettled"
    source := ⟨"glass-2025", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex thinks there's a meeting."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "It is open whether there is a meeting."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "think"), ("state", "unsettled")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2a_notP : LinguisticExample :=
  { id := "glass2025_2a_notP"
    source := ⟨"glass-2025", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alex thinks there's a meeting."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "There is no meeting."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "think"), ("state", "notP")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4_notP : LinguisticExample :=
  { id := "glass2025_4_notP"
    source := ⟨"glass-2023", "(4)"⟩
    reportedIn := some ⟨"glass-2025", "(4)"⟩
    language := "mand1415"
    primaryText := "Māma yǐwéi wǒ bìng le"
    discourseSegments := []
    glossedTokens := [("Māma", "mom"), ("yǐwéi", "yǐwéi"), ("wǒ", "1sg"), ("bìng", "sick"), ("le", "asp")]
    translation := "Mom is under the impression that I'm sick."
    context := "The speaker faked illness to avoid school."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "yiwei"), ("state", "notP")]
    comment := "Excerpted from Glass 2023, p. 2."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4_p : LinguisticExample :=
  { id := "glass2025_4_p"
    source := ⟨"glass-2023", "(4)"⟩
    reportedIn := some ⟨"glass-2025", "(4)"⟩
    language := "mand1415"
    primaryText := "Māma yǐwéi wǒ bìng le"
    discourseSegments := []
    glossedTokens := [("Māma", "mom"), ("yǐwéi", "yǐwéi"), ("wǒ", "1sg"), ("bìng", "sick"), ("le", "asp")]
    translation := "Mom is under the impression that I'm sick."
    context := "The speaker is definitely sick."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "yiwei"), ("state", "p")]
    comment := "Nonsensical if the speaker is definitely sick."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5_notP : LinguisticExample :=
  { id := "glass2025_5_notP"
    source := ⟨"glass-2023", "(5)"⟩
    reportedIn := some ⟨"glass-2025", "(5)"⟩
    language := "mand1415"
    primaryText := "Māma rènwéi wǒ bìng le"
    discourseSegments := []
    glossedTokens := [("Māma", "mom"), ("rènwéi", "think"), ("wǒ", "1sg"), ("bìng", "sick"), ("le", "asp")]
    translation := "Mom thinks I'm sick."
    context := "The speaker faked illness to avoid school."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "renwei"), ("state", "notP")]
    comment := "Adapted from Glass 2023, p. 2."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5_unsettled : LinguisticExample :=
  { id := "glass2025_5_unsettled"
    source := ⟨"glass-2023", "(5)"⟩
    reportedIn := some ⟨"glass-2025", "(5)"⟩
    language := "mand1415"
    primaryText := "Māma rènwéi wǒ bìng le"
    discourseSegments := []
    glossedTokens := [("Māma", "mom"), ("rènwéi", "think"), ("wǒ", "1sg"), ("bìng", "sick"), ("le", "asp")]
    translation := "Mom thinks I'm sick."
    context := "The speaker feels exhausted and thinks she may indeed be sick, citing her mother's belief as evidence."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "renwei"), ("state", "unsettled")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7 : LinguisticExample :=
  { id := "glass2025_7"
    source := ⟨"glass-2023", "(7)"⟩
    reportedIn := some ⟨"glass-2025", "(7)"⟩
    language := "mand1415"
    primaryText := "wǒ bù zhīdào yǒu-méi-yǒu défēn, dànshì zhège qiúyuán yǐwéi défēn le"
    discourseSegments := []
    glossedTokens := [("wǒ", "I"), ("bù", "not"), ("zhīdào", "know"), ("yǒu-méi-yǒu", "have-not-have"), ("défēn", "score"), ("dànshì", "but"), ("zhège", "this-cl"), ("qiúyuán", "ball-player"), ("yǐwéi", "yǐwéi"), ("défēn", "score"), ("le", "asp")]
    translation := "I don't know whether the player scored or not, but he's under the impression that he did."
    context := "The athlete caught the ball on the edge of the end zone and celebrates while the referees debate the catch; the speaker does not know whether he scored."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb", "yiwei"), ("state", "unsettled")]
    comment := "Glass 2023, p. 6. Odd if the speaker has no reason to question the athlete's belief; a presupposition of not-p would contradict the ignorance expressed in the first clause."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1a, ex_2a_p, ex_2a_unsettled, ex_2a_notP, ex_4_notP, ex_4_p, ex_5_notP, ex_5_unsettled, ex_7]

end Glass2025.Examples
