module

public import Linglib.Data.Examples.Schema

/-!
# `Xiang2022` — typed example data

Auto-generated from `Linglib/Data/Examples/Xiang2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Xiang2022.Examples`.
-/

@[expose] public section

namespace Xiang2022.Examples

open Data.Examples

def ex_1 : LinguisticExample :=
  { id := "xiang2022_1"
    source := ⟨"xiang-2022", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who went to the party? John and Mary."
    discourseSegments := []
    glossedTokens := []
    translation := "Who went to the party? John and Mary."
    context := "A believes that among the relevant individuals only John and Mary went to the party."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("answer", "complete")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_2 : LinguisticExample :=
  { id := "xiang2022_2"
    source := ⟨"xiang-2022", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who went to the party? Antonio did ..."
    discourseSegments := []
    glossedTokens := []
    translation := "Who went to the party? Antonio did ..."
    context := "A believes Antonio went to the party and it is unclear who else did."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("answer", "partial"), ("contour", "rise-fall-rise")]
    comment := "A marked partial answer."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3 : LinguisticExample :=
  { id := "xiang2022_3"
    source := ⟨"xiang-2022", "(2b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who went to the party? Antonio did."
    discourseSegments := []
    glossedTokens := []
    translation := "Who went to the party? Antonio did."
    context := "A believes Antonio went to the party and it is unclear who else did."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("answer", "partial"), ("contour", "falling")]
    comment := "An unmarked partial answer yields a misleading exclusivity inference."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4 : LinguisticExample :=
  { id := "xiang2022_4"
    source := ⟨"xiang-2022", "(3)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Where can we go to get coffee?"
    discourseSegments := []
    glossedTokens := []
    translation := "Where can we go to get coffee?"
    context := "There are three coffee places nearby: Starbucks, Peet's, and J.P. Licks."
    judgment := .acceptable
    alternatives := [("Starbucks.", .acceptable), ("Starbucks, Peet's, and J.P. Licks.", .acceptable), ("Starbucks, Peet's, or J.P. Licks.", .acceptable)]
    readings := [("mention-some", .acceptable), ("conjunctive mention-all", .acceptable), ("disjunctive mention-all", .acceptable)]
    paperFeatures := [("modal", "can"), ("flavor", "teleological")]
    comment := "The mention-some answer carries no exclusivity inference."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_5 : LinguisticExample :=
  { id := "xiang2022_5"
    source := ⟨"xiang-2022", "(5)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John left for coffee 15 mins ago. Where could he have gone?"
    discourseSegments := []
    glossedTokens := []
    translation := "John left for coffee 15 mins ago. Where could he have gone?"
    context := "A believes there are two coffee places nearby, Starbucks and Peet's, and that John frequents both."
    judgment := .acceptable
    alternatives := [("Starbucks.", .questionable), ("Starbucks or Peet's.", .acceptable)]
    readings := []
    paperFeatures := [("modal", "could"), ("flavor", "epistemic")]
    comment := "An epistemic modal does not license mention-some without contextual support."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6 : LinguisticExample :=
  { id := "xiang2022_6"
    source := ⟨"xiang-2022", "(8)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Where should I get coffee?"
    discourseSegments := []
    glossedTokens := []
    translation := "Where should I get coffee?"
    context := "A believes there are two coffee places nearby, Starbucks and Peet's."
    judgment := .acceptable
    alternatives := [("Starbucks.", .questionable), ("Starbucks or Peet's. Either is good.", .acceptable)]
    readings := []
    paperFeatures := [("modal", "should"), ("force", "universal")]
    comment := "A universal modal does not license mention-some."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7 : LinguisticExample :=
  { id := "xiang2022_7"
    source := ⟨"xiang-2022", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who can teach Psycholinguistics? Judy can."
    discourseSegments := []
    glossedTokens := []
    translation := "Who can teach Psycholinguistics? Judy can."
    context := "The hiring committee wants to prioritize the candidates on the long-list who can teach Psycholinguistics."
    judgment := .acceptable
    alternatives := []
    readings := [("mention-all", .acceptable)]
    paperFeatures := [("modal", "can"), ("goal", "exhaustive")]
    comment := "An exhaustive conversational goal blocks mention-some."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8 : LinguisticExample :=
  { id := "xiang2022_8"
    source := ⟨"xiang-2022", "(58)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which child came?"
    discourseSegments := []
    glossedTokens := []
    translation := "Which child came?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("only one of the children came", .acceptable)]
    paperFeatures := [("wh", "singular"), ("inference", "uniqueness")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_9 : LinguisticExample :=
  { id := "xiang2022_9"
    source := ⟨"xiang-2022", "(60a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which children came?"
    discourseSegments := []
    glossedTokens := []
    translation := "Which children came?"
    context := "Among the children under consideration only Andy and Billy came; the speaker knows multiple children came but not who."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("wh", "plural")]
    comment := "The sum-based answer is exhaustive."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_10 : LinguisticExample :=
  { id := "xiang2022_10"
    source := ⟨"xiang-2022", "(60b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which child came?"
    discourseSegments := []
    glossedTokens := []
    translation := "Which child came?"
    context := "Among the children under consideration only Andy and Billy came; the speaker knows multiple children came but not who."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("wh", "singular")]
    comment := "No exhaustive true answer: Dayal's presupposition fails."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_11 : LinguisticExample :=
  { id := "xiang2022_11"
    source := ⟨"xiang-2022", "(61)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which textbook should I use for this class? Heim & Kratzer or Meaning & Grammar. The choice is up to you."
    discourseSegments := []
    glossedTokens := []
    translation := "Which textbook should I use for this class? Heim & Kratzer or Meaning & Grammar. The choice is up to you."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("narrow-scope disjunction", .acceptable)]
    paperFeatures := [("wh", "singular"), ("answer", "higher-order disjunction")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_12 : LinguisticExample :=
  { id := "xiang2022_12"
    source := ⟨"xiang-2022", "(62)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which textbook can I use for this class?"
    discourseSegments := []
    glossedTokens := []
    translation := "Which textbook can I use for this class?"
    context := ""
    judgment := .acceptable
    alternatives := [("Heim & Kratzer or Meaning & Grammar.", .acceptable), ("Heim & Kratzer and Meaning & Grammar.", .unacceptable)]
    readings := []
    paperFeatures := [("wh", "singular"), ("asymmetry", "disjunction-conjunction")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_13 : LinguisticExample :=
  { id := "xiang2022_13"
    source := ⟨"xiang-2022", "(68a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which letter could we add to fo_m to form a word? A or r."
    discourseSegments := []
    glossedTokens := []
    translation := "Which letter could we add to fo_m to form a word? A or r."
    context := "A multiple-choice context in which each choice involves a single letter, either a or r."
    judgment := .acceptable
    alternatives := []
    readings := [("local uniqueness", .acceptable)]
    paperFeatures := [("modal", "could"), ("inference", "local uniqueness")]
    comment := "The unique letter that we add could be a and could be r."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_14 : LinguisticExample :=
  { id := "xiang2022_14"
    source := ⟨"xiang-2022", "(69)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which chapter do we have to assign to the students? Chap. 1 or Chap. 2, either is good."
    discourseSegments := []
    glossedTokens := []
    translation := "Which chapter do we have to assign to the students? Chap. 1 or Chap. 2, either is good."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("we are not allowed to assign more than one chapter", .acceptable)]
    paperFeatures := [("modal", "have to"), ("inference", "local uniqueness")]
    comment := "Local uniqueness is independent of modal force."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_15 : LinguisticExample :=
  { id := "xiang2022_15"
    source := ⟨"xiang-2022", "(83)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I know which chapter we can assign to the students next week ..., Chap. 3."
    discourseSegments := []
    glossedTokens := []
    translation := "I know which chapter we can assign to the students next week ..., Chap. 3."
    context := "The book has three chapters. The instructor has told the speaker, a TA, that they could assign either Chap. 1, or Chap. 2, or both Chaps. 2 and 3 next week."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "can"), ("inference", "local uniqueness")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_16 : LinguisticExample :=
  { id := "xiang2022_16"
    source := ⟨"xiang-2022", "(84b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I know which SINgle chapter we can assign ..., Chap. 1."
    discourseSegments := []
    glossedTokens := []
    translation := "I know which SINgle chapter we can assign ..., Chap. 1."
    context := "As in (83)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "can"), ("exhaustification", "local")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_17 : LinguisticExample :=
  { id := "xiang2022_17"
    source := ⟨"xiang-2022", "(85)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We should assign one or two papers. Got it. Which paper could we assign?"
    discourseSegments := []
    glossedTokens := []
    translation := "We should assign one or two papers. Got it. Which paper could we assign?"
    context := ""
    judgment := .questionable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "could"), ("inference", "local uniqueness")]
    comment := "Nine of eleven speakers found the question unnatural: it suggests at most one paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_18 : LinguisticExample :=
  { id := "xiang2022_18"
    source := ⟨"xiang-2022", "(86)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "We should assign a journal article or a book chapter. Got it. Which journal article could we assign?"
    discourseSegments := []
    glossedTokens := []
    translation := "We should assign a journal article or a book chapter. Got it. Which journal article could we assign?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "could")]
    comment := "A sub-question of the instructor's request."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_19 : LinguisticExample :=
  { id := "xiang2022_19"
    source := ⟨"xiang-2022", "(102)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which chapter do we have to assign? Chap. 1."
    discourseSegments := []
    glossedTokens := []
    translation := "Which chapter do we have to assign? Chap. 1."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("global uniqueness", .acceptable)]
    paperFeatures := [("modal", "have to"), ("interpretation", "first-order")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_20 : LinguisticExample :=
  { id := "xiang2022_20"
    source := ⟨"xiang-2022", "(103)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which chapter do we have to assign? Chap. 1 or Chap. 2, either is good."
    discourseSegments := []
    glossedTokens := []
    translation := "Which chapter do we have to assign? Chap. 1 or Chap. 2, either is good."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("local uniqueness", .acceptable)]
    paperFeatures := [("modal", "have to"), ("interpretation", "narrow-scope higher-order")]
    comment := "In the scenario where some accessible world assigns both chapters, only Relativized Exhaustivity is violated."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_21 : LinguisticExample :=
  { id := "xiang2022_21"
    source := ⟨"xiang-2022", "(105b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which chapter can we assign?"
    discourseSegments := []
    glossedTokens := []
    translation := "Which chapter can we assign?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("universal local uniqueness", .acceptable)]
    paperFeatures := [("modal", "can"), ("interpretation", "mention-some")]
    comment := "We can assign exactly one chapter, but not more."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_22 : LinguisticExample :=
  { id := "xiang2022_22"
    source := ⟨"xiang-2022", "(106)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which SINgle chapter can we assign?"
    discourseSegments := []
    glossedTokens := []
    translation := "Which SINgle chapter can we assign?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("existential local uniqueness", .acceptable)]
    paperFeatures := [("modal", "can"), ("exhaustification", "local")]
    comment := "Only the accessible worlds where exactly one chapter is assigned matter."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23 : LinguisticExample :=
  { id := "xiang2022_23"
    source := ⟨"xiang-2022", "(107)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which chapter can we assign?"
    discourseSegments := []
    glossedTokens := []
    translation := "Which chapter can we assign?"
    context := ""
    judgment := .acceptable
    alternatives := [("Chap. 1 or Chap. 2.", .acceptable), ("Chap. 1 and Chap. 2.", .unacceptable)]
    readings := [("disjunctive mention-all", .acceptable)]
    paperFeatures := [("modal", "can"), ("wh", "singular")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1, ex_2, ex_3, ex_4, ex_5, ex_6, ex_7, ex_8, ex_9, ex_10, ex_11, ex_12, ex_13, ex_14, ex_15, ex_16, ex_17, ex_18, ex_19, ex_20, ex_21, ex_22, ex_23]

end Xiang2022.Examples
