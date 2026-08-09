import Linglib.Data.Examples.Schema

/-!
# `Hacquard2006` — typed example data

Auto-generated from `Linglib/Data/Examples/Hacquard2006.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Hacquard2006.Examples`.
-/

namespace Hacquard2006.Examples

open Data.Examples

def ex1a : LinguisticExample :=
  { id := "hacquard2006_ex1a"
    source := ⟨"hacquard-2006", "(1a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Pour aller au zoo, Jane pouvait prendre le train."
    discourseSegments := []
    glossedTokens := [("Pour", "to"), ("aller", "go"), ("au", "to-the"), ("zoo", "zoo"), ("Jane", "Jane"), ("pouvait", "can-PST.IPFV"), ("prendre", "take"), ("le", "the"), ("train", "train")]
    translation := "To go to the zoo, Jane could take the train."
    context := "Goal-oriented pouvoir with imparfait. Compatible with a scenario in which Jane did not take the train (nor went to the zoo)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "imperfective"), ("actualityEntailment", "false"), ("flavor", "goal-oriented")]
    comment := "Ch. 1 opening minimal pair with (1b): perfective on the modal forces actualization of the complement, imperfective does not."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex1b : LinguisticExample :=
  { id := "hacquard2006_ex1b"
    source := ⟨"hacquard-2006", "(1b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Pour aller au zoo, Jane a pu prendre le train."
    discourseSegments := []
    glossedTokens := [("Pour", "to"), ("aller", "go"), ("au", "to-the"), ("zoo", "zoo"), ("Jane", "Jane"), ("a pu", "can-PST.PFV"), ("prendre", "take"), ("le", "the"), ("train", "train")]
    translation := "To go to the zoo, Jane was able to take the train."
    context := "Goal-oriented pouvoir with passé composé. True only if Jane actually took the train; denying the complement yields a contradiction."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "perfective"), ("actualityEntailment", "true"), ("flavor", "goal-oriented")]
    comment := "Ch. 1 opening minimal pair with (1a)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex2a : LinguisticExample :=
  { id := "hacquard2006_ex2a"
    source := ⟨"bhatt-1999", "(2a)"⟩
    reportedIn := some ⟨"hacquard-2006", "(2a)"⟩
    language := "stan1293"
    primaryText := "Yesterday, firemen were able to eat 50 apples."
    discourseSegments := []
    glossedTokens := []
    translation := "Yesterday, firemen were able to eat 50 apples."
    context := "English lacks overt perfective/imperfective morphology; the episodic adverbial 'yesterday' forces the perfective-like reading, which is implicative."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "perfective"), ("actualityEntailment", "true"), ("flavor", "ability")]
    comment := "Bhatt's adverbial pair, reproduced by the dissertation to show the English analogue of the aspect split."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex2b : LinguisticExample :=
  { id := "hacquard2006_ex2b"
    source := ⟨"bhatt-1999", "(2b)"⟩
    reportedIn := some ⟨"hacquard-2006", "(2b)"⟩
    language := "stan1293"
    primaryText := "Back in the days, firemen were able to eat 50 apples."
    discourseSegments := []
    glossedTokens := []
    translation := "Back in the days, firemen were able to eat 50 apples."
    context := "The habitual adverbial 'back in the days' forces the imperfective-like reading, which is non-implicative."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "imperfective"), ("actualityEntailment", "false"), ("flavor", "ability")]
    comment := "Bhatt's adverbial pair, reproduced by the dissertation to show the English analogue of the aspect split."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex22a : LinguisticExample :=
  { id := "hacquard2006_ex22a"
    source := ⟨"hacquard-2006", "(22a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Jane a pu soulever cette table, #mais elle ne l'a pas soulevée."
    discourseSegments := []
    glossedTokens := [("Jane", "Jane"), ("a pu", "can-PST.PFV"), ("soulever", "lift"), ("cette", "this"), ("table", "table"), ("mais", "but"), ("elle", "she"), ("ne", "NEG"), ("l'", "it"), ("a", "has"), ("pas", "NEG"), ("soulevée", "lifted")]
    translation := "Jane could lift this table, #but she didn't lift it."
    context := "Ability pouvoir with passé composé plus a continuation denying the complement: the continuation contradicts the actuality entailment."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "perfective"), ("actualityEntailment", "true"), ("flavor", "ability")]
    comment := "With perfective morphology pouvoir behaves like an implicative predicate (manage): the complement must hold in the actual world."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex23a : LinguisticExample :=
  { id := "hacquard2006_ex23a"
    source := ⟨"hacquard-2006", "(23a)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Jane pouvait soulever cette table, mais elle ne l'a pas soulevée."
    discourseSegments := []
    glossedTokens := [("Jane", "Jane"), ("pouvait", "can-PST.IPFV"), ("soulever", "lift"), ("cette", "this"), ("table", "table"), ("mais", "but"), ("elle", "she"), ("ne", "NEG"), ("l'", "it"), ("a", "has"), ("pas", "NEG"), ("soulevée", "lifted")]
    translation := "Jane could lift this table, but she didn't lift it."
    context := "Ability pouvoir with imparfait plus the same denial continuation: no contradiction, so no actuality entailment."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "imperfective"), ("actualityEntailment", "false"), ("flavor", "ability")]
    comment := "Imperfective counterpart of (22a)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex22b : LinguisticExample :=
  { id := "hacquard2006_ex22b"
    source := ⟨"hacquard-2006", "(22b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Jane ha potuto sollevare questo tavolo, #ma non lo ha fatto."
    discourseSegments := []
    glossedTokens := [("Jane", "Jane"), ("ha potuto", "can-PST.PFV"), ("sollevare", "lift"), ("questo", "this"), ("tavolo", "table"), ("ma", "but"), ("non", "NEG"), ("lo", "it"), ("ha fatto", "did")]
    translation := "Jane could lift this table, #but she didn't do it."
    context := "Italian potere with passato prossimo: same actuality entailment as French (22a)."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "perfective"), ("actualityEntailment", "true"), ("flavor", "ability")]
    comment := "Italian member of the (22) pair."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex23b : LinguisticExample :=
  { id := "hacquard2006_ex23b"
    source := ⟨"hacquard-2006", "(23b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Jane poteva sollevare questo tavolo, ma non lo ha fatto."
    discourseSegments := []
    glossedTokens := [("Jane", "Jane"), ("poteva", "can-PST.IPFV"), ("sollevare", "lift"), ("questo", "this"), ("tavolo", "table"), ("ma", "but"), ("non", "NEG"), ("lo", "it"), ("ha fatto", "did")]
    translation := "Jane could lift this table, but she didn't do it."
    context := "Italian potere with imperfetto: no actuality entailment, as in French (23a)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("aspect", "imperfective"), ("actualityEntailment", "false"), ("flavor", "ability")]
    comment := "Italian member of the (23) pair."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex201 : LinguisticExample :=
  { id := "hacquard2006_ex201"
    source := ⟨"hacquard-2006", "(201)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Jane a dû prendre le train."
    discourseSegments := []
    glossedTokens := [("Jane", "Jane"), ("a dû", "must-PST.PFV"), ("prendre", "take"), ("le", "the"), ("train", "train")]
    translation := "Jane must have taken / had to take the train."
    context := "Ambiguous between an epistemic reading relativized to the speaker's evidence at utterance time and a goal-oriented reading relativized to Jane's circumstances at a past time."
    judgment := .acceptable
    alternatives := []
    readings := [("epistemic: given my evidence now, Jane must have taken the train", .acceptable), ("goal-oriented: given Jane's circumstances then, Jane had to take the train", .acceptable)]
    paperFeatures := []
    comment := "The event-binding ambiguity: speech-event binding yields the epistemic reading (speaker, now); aspect binding yields the goal-oriented reading (Jane, then)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex247b : LinguisticExample :=
  { id := "hacquard2006_ex247b"
    source := ⟨"hacquard-2006", "(247b)"⟩
    reportedIn := none
    language := "stan1290"
    primaryText := "Jane a pu penser que Darcy aimait Lizzie."
    discourseSegments := []
    glossedTokens := [("Jane", "Jane"), ("a pu", "can-PST.PFV"), ("penser", "think"), ("que", "that"), ("Darcy", "Darcy"), ("aimait", "loved"), ("Lizzie", "Lizzie")]
    translation := "Jane might have thought that Darcy loved Lizzie."
    context := "A low modal is normally barred from epistemic readings because the VP event lacks propositional content; here the complement supplies a contentful thinking event."
    judgment := .acceptable
    alternatives := []
    readings := [("speech-bound epistemic: possible given the speaker's evidence", .acceptable), ("aspect-bound epistemic: an epistemic necessity for Jane at a past belief state", .questionable)]
    paperFeatures := []
    comment := "Attributed to K. von Fintel (p.c.). The speech-bound reading is clearly more salient; eventive attitudes (see/notice) make the aspect-bound reading easier and implicative."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex1a, ex1b, ex2a, ex2b, ex22a, ex23a, ex22b, ex23b, ex201, ex247b]

end Hacquard2006.Examples
