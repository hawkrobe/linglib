module

public import Linglib.Data.Examples.Schema

/-!
# `Sidner1979` — typed example data

Auto-generated from `Linglib/Data/Examples/Sidner1979.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Sidner1979.Examples`.
-/

@[expose] public section

namespace Sidner1979.Examples

open Data.Examples

def ex_22 : LinguisticExample :=
  { id := "sidner1979_22"
    source := ⟨"sidner-1979", "(22)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I took my sister to the zoo today."
    discourseSegments := ["I took my sister to the zoo today."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "expectedFocus"), ("form", "plain"), ("expectedFocus", "my sister")]
    comment := "Not an is-a or there-insertion sentence: the default expected focus list runs my sister (theme), the zoo, today, I (agent), the verb phrase, and the expected focus is its first member."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23 : LinguisticExample :=
  { id := "sidner1979_23"
    source := ⟨"sidner-1979", "(23)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "There once was an old man who lived in the woods."
    discourseSegments := ["There once was an old man who lived in the woods."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "expectedFocus"), ("form", "thereInsertion"), ("expectedFocus", "an old man")]
    comment := "A there-insertion sentence: the expected focus is its subject."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_24 : LinguisticExample :=
  { id := "sidner1979_24"
    source := ⟨"sidner-1979", "(24)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Linda talked with her dog all day long."
    discourseSegments := ["Linda talked with her dog all day long."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "expectedFocus"), ("form", "plain"), ("expectedFocus", "her dog")]
    comment := "No theme is present, what is talked about not being given: the default expected focus list runs her dog, all day long, Linda (agent), the verb phrase."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def d2 : LinguisticExample :=
  { id := "sidner1979_d2"
    source := ⟨"sidner-1979", "D2 (chapter 4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary is giving a surprise party at Hilda's house. It's at 340 Cherry St."
    discourseSegments := ["Mary is giving a surprise party at Hilda's house.", "It's at 340 Cherry St."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("it = Hilda's house", .acceptable)]
    paperFeatures := [("phenomenon", "recencyRule")]
    comment := "The pronoun in subject position co-specifies Hilda's house, the last constituent of the previous sentence, by the recency rule rather than the expected focus."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def d7 : LinguisticExample :=
  { id := "sidner1979_d7"
    source := ⟨"sidner-1979", "D7 (chapter 4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I lost a necklace at the office yesterday. I inherited it from my grandmother, and it meant a lot to me."
    discourseSegments := ["I lost a necklace at the office yesterday.", "I inherited it from my grandmother,", "and it meant a lot to me."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("it = the necklace", .acceptable)]
    paperFeatures := [("phenomenon", "nonAgentPronoun")]
    comment := "The pronoun outside agent position co-specifies the discourse focus, the necklace; the alternate potential focus, the office, is never considered."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def d8 : LinguisticExample :=
  { id := "sidner1979_d8"
    source := ⟨"sidner-1979", "D8 (chapter 4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Yesterday Max went to Bloomingdales with Ned and Winston on a shopping trip. While he was there, he bought some sneakers for his mother."
    discourseSegments := ["Yesterday Max went to Bloomingdales with Ned and Winston on a shopping trip.", "While he was there, he bought some sneakers for his mother."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("he = Max", .acceptable)]
    paperFeatures := [("phenomenon", "agentPronoun")]
    comment := "The pronoun in agent position co-specifies the actor focus, Max: the discourse focus, Bloomingdales, was established in the same sentence and takes no precedence, and the two potential actors Ned and Winston raise no actor ambiguity."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def d9 : LinguisticExample :=
  { id := "sidner1979_d9"
    source := ⟨"sidner-1979", "D9 (chapter 4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I haven't seen Jeff for several days. Carl thinks he's studying for his exams. Oscar says he is sick, but I think he went to the Cape with Linda."
    discourseSegments := ["I haven't seen Jeff for several days.", "Carl thinks he's studying for his exams.", "Oscar says he is sick,", "but I think he went to the Cape with Linda."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("he = Jeff throughout", .acceptable)]
    paperFeatures := [("phenomenon", "animateDiscourseFocusRule")]
    comment := "The discourse focus is Jeff while the actor focus moves from the speaker to Carl to Oscar; every he co-specifies Jeff, the discourse focus having been established before any other phrase satisfying person, number and gender. Reported as (34) in Grosz, Joshi and Weinstein (1995)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def d14a : LinguisticExample :=
  { id := "sidner1979_d14a"
    source := ⟨"sidner-1979", "D14 (chapter 4), 2a"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I took my dog to the vet yesterday. He bit him in the hand."
    discourseSegments := ["I took my dog to the vet yesterday.", "He bit him in the hand."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("he = my dog, him = the vet", .acceptable)]
    paperFeatures := [("phenomenon", "actorAndDiscourseFocus")]
    comment := "The actor focus, the speaker, fails the syntactic filters for he, so the first potential actor, my dog, is its co-specification; the discourse focus, my dog, is rejected for him by inference, dogs having no hands, so the first potential discourse focus, the vet, is its co-specification. The discourse focus moves to the vet and my dog is stacked; the actor focus moves to my dog and the speaker is stacked."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def d14b : LinguisticExample :=
  { id := "sidner1979_d14b"
    source := ⟨"sidner-1979", "D14 (chapter 4), 2b"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "I took my dog to the vet yesterday. He injected him with a new medicine."
    discourseSegments := ["I took my dog to the vet yesterday.", "He injected him with a new medicine."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("he = the vet, him = my dog", .acceptable)]
    paperFeatures := [("phenomenon", "actorAndDiscourseFocus")]
    comment := "The discourse focus, my dog, is retained as the co-specification of him, a dog being injectable; for he the actor focus and the first potential actor are rejected, dogs giving no injections, and the vet is its co-specification and the new actor focus."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def d25 : LinguisticExample :=
  { id := "sidner1979_d25"
    source := ⟨"sidner-1979", "D25 (chapter 2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Last week there were some nice strawberries in the refrigerator. They came from our food co-op and were unusually fresh."
    discourseSegments := ["Last week there were some nice strawberries in the refrigerator.", "They came from our food co-op and were unusually fresh."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("they = the strawberries", .acceptable)]
    paperFeatures := [("phenomenon", "focusConfirmation")]
    comment := "A there-insertion sentence whose subject, some strawberries, is the expected focus; the pronoun of the second sentence co-specifies it and the focus is retained at step 4 of the focusing algorithm."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def d35 : LinguisticExample :=
  { id := "sidner1979_d35"
    source := ⟨"sidner-1979", "D35 (chapter 2)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Alfred and Zohar liked to play baseball. They played it everyday after school before dinner. After their game, Alfred and Zohar had ice cream cones. They tasted really good. Alfred always had the vanilla super scooper, while Zohar tried the flavor of the day cone. After the cones had been eaten, the boys went home to study."
    discourseSegments := ["Alfred and Zohar liked to play baseball.", "They played it everyday after school before dinner.", "After their game, Alfred and Zohar had ice cream cones.", "They tasted really good.", "Alfred always had the vanilla super scooper,", "while Zohar tried the flavor of the day cone.", "After the cones had been eaten,", "the boys went home to study."]
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("they in the fourth sentence = the ice cream cones", .acceptable)]
    paperFeatures := [("phenomenon", "focusMovement")]
    comment := "The expected focus is baseball, the theme of the verb complement, confirmed by it in the second sentence while they in agent position is not consulted; the fourth sentence's they co-specifies the alternate ice cream cones and the focus moves there, baseball being stacked."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_22, ex_23, ex_24, d2, d7, d8, d9, d14a, d14b, d25, d35]

end Sidner1979.Examples
