import Linglib.Data.Examples.Schema

/-!
# `Ginzburg2012` — typed example data

Auto-generated from `Linglib/Data/Examples/Ginzburg2012.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Ginzburg2012.Examples`.
-/

namespace Ginzburg2012.Examples

open Data.Examples

def ex_22a : LinguisticExample :=
  { id := "ginzburg2012_22a"
    source := ⟨"ginzburg-2012", "(22a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Who does Bo admire? B: Bo?"
    discourseSegments := ["A: Who does Bo admire?", "B: Bo?"]
    glossedTokens := []
    translation := "A: Who does Bo admire? B: Bo?"
    context := "The addressee reprises the name. Three readings: short answer 'Does Bo admire Bo?', clausal confirmation 'Are you asking who Bo (of all people) admires?', intended content 'Who do you mean Bo?'."
    judgment := .acceptable
    alternatives := []
    readings := [("short answer", .acceptable), ("clausal confirmation", .acceptable), ("intended content", .acceptable)]
    paperFeatures := [("speaker", "addressee")]
    comment := "Against Equal Access to Context: only the addressee has the two clarification readings."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_22b : LinguisticExample :=
  { id := "ginzburg2012_22b"
    source := ⟨"ginzburg-2012", "(22b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Who does Bo admire? Bo?"
    discourseSegments := ["A: Who does Bo admire?", "A: Bo?"]
    glossedTokens := []
    translation := "A: Who does Bo admire? Bo?"
    context := "The original speaker reprises the name: short answer 'Does Bo admire Bo?' or self-correction 'Did I say Bo?'."
    judgment := .acceptable
    alternatives := []
    readings := [("short answer", .acceptable), ("self-correction", .acceptable)]
    paperFeatures := [("speaker", "original speaker")]
    comment := "Only the original speaker has the self-correction reading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23a : LinguisticExample :=
  { id := "ginzburg2012_23a"
    source := ⟨"ginzburg-2012", "(23a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Which members of this audience own a parakeet? Why?"
    discourseSegments := ["A: Which members of this audience own a parakeet?", "A: Why?"]
    glossedTokens := []
    translation := "A: Which members of this audience own a parakeet? Why?"
    context := "A keeps the turn: 'Why?' = 'Why own a parakeet?'."
    judgment := .acceptable
    alternatives := []
    readings := [("why own a parakeet", .acceptable)]
    paperFeatures := [("turn", "kept")]
    comment := "The Turn-Taking Puzzle: resolution of bare 'why' depends on who holds the turn."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23b : LinguisticExample :=
  { id := "ginzburg2012_23b"
    source := ⟨"ginzburg-2012", "(23b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Which members of this audience own a parakeet? B: Why?"
    discourseSegments := ["A: Which members of this audience own a parakeet?", "B: Why?"]
    glossedTokens := []
    translation := "A: Which members of this audience own a parakeet? B: Why?"
    context := "B takes the turn: 'Why?' = 'Why are you asking which members of this audience own a parakeet?'."
    judgment := .acceptable
    alternatives := []
    readings := [("why are you asking", .acceptable)]
    paperFeatures := [("turn", "taken")]
    comment := "The reading available to B is unavailable to A in (23a), and vice versa."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_23c : LinguisticExample :=
  { id := "ginzburg2012_23c"
    source := ⟨"ginzburg-2012", "(23c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Which members of this audience own a parakeet? Why am I asking this question?"
    discourseSegments := ["A: Which members of this audience own a parakeet?", "A: Why am I asking this question?"]
    glossedTokens := []
    translation := "A: Which members of this audience own a parakeet? Why am I asking this question?"
    context := "The resolution unavailable to A with bare 'Why?' is a coherent follow-up when expressed non-elliptically."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("turn", "kept")]
    comment := "Shows the (23a)/(23b) asymmetry is not a matter of coherence or plausibility."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_54 : LinguisticExample :=
  { id := "ginzburg2012_54"
    source := ⟨"ginzburg-2012", "(54)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Hi. B: Hi. A: Who's coming tomorrow? B: Several colleagues of mine (are coming). A: I see. B: Mike (is coming) too."
    discourseSegments := ["A: Hi.", "B: Hi.", "A: Who's coming tomorrow?", "B: Several colleagues of mine (are coming).", "A: I see.", "B: Mike (is coming) too."]
    glossedTokens := []
    translation := "A: Hi. B: Hi. A: Who's coming tomorrow? B: Several colleagues of mine (are coming). A: I see. B: Mike (is coming) too."
    context := "Conversation-initial exchange traced through greeting, counter-greeting, Free Speech, Ask QUD-incrementation, QSPEC, Assert QUD-incrementation, Accept and Fact update/QUD-downdate."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_65 : LinguisticExample :=
  { id := "ginzburg2012_65"
    source := ⟨"ginzburg-2012", "(65)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Who should we invite for tomorrow? B: Who will agree to come? A: Helen and Jelle and Fran and maybe Sunil. B: (a) I see. (b) So, Jelle I think. A: OK."
    discourseSegments := ["A: Who should we invite for tomorrow?", "B: Who will agree to come?", "A: Helen and Jelle and Fran and maybe Sunil.", "B: (a) I see. (b) So, Jelle I think.", "A: OK."]
    glossedTokens := []
    translation := "A: Who should we invite for tomorrow? B: Who will agree to come? A: Helen and Jelle and Fran and maybe Sunil. B: (a) I see. (b) So, Jelle I think. A: OK."
    context := "B's question influences A's; A's answer resolves B's question and is accepted, leaving A's question QUD-maximal."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Traced in (66)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_67 : LinguisticExample :=
  { id := "ginzburg2012_67"
    source := ⟨"ginzburg-2012", "(67)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: (a) Bo is now in Essen, (b) is he? B: Yes."
    discourseSegments := ["A: (a) Bo is now in Essen, (b) is he?", "B: Yes."]
    glossedTokens := []
    translation := "A: (a) Bo is now in Essen, (b) is he? B: Yes."
    context := "The asserter checks their own assertion; the addressee confirms."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Traced in (68)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_78 : LinguisticExample :=
  { id := "ginzburg2012_78"
    source := ⟨"ginzburg-2012", "(78)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: (1a) Who will Max be inviting? (1b) When will these guests be arriving? B: Mary and Bill. A: Aha. B: Tomorrow or the day after most likely."
    discourseSegments := ["A: (1a) Who will Max be inviting? (1b) When will these guests be arriving?", "B: Mary and Bill.", "A: Aha.", "B: Tomorrow or the day after most likely."]
    glossedTokens := []
    translation := "A: (1a) Who will Max be inviting? (1b) When will these guests be arriving? B: Mary and Bill. A: Aha. B: Tomorrow or the day after most likely."
    context := "Successive questions by one speaker: the second does not influence the first, which stays QUD-maximal and is answered first."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := []
    comment := "Traced in (79)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_95 : LinguisticExample :=
  { id := "ginzburg2012_95"
    source := ⟨"ginzburg-2012", "(95)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Hi. B: I'm off. A: OK. B: Bye."
    discourseSegments := ["A: Hi.", "B: I'm off.", "A: OK.", "B: Bye."]
    glossedTokens := []
    translation := "A: Hi. B: I'm off. A: OK. B: Bye."
    context := "B takes the genre to be CasualChat, whose anticipated issues are how A is and how B is; 'I'm off' is an initiating move about the latter."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("genre", "CasualChat")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ch6_90 : LinguisticExample :=
  { id := "ginzburg2012_ch6_90"
    source := ⟨"ginzburg-2012", "Ch. 6 (90)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Is George here? B: Is WHO here? A: George Sand. B: Ah, no."
    discourseSegments := ["A: Is George here?", "B: Is WHO here?", "A: George Sand.", "B: Ah, no."]
    glossedTokens := []
    translation := "A: Is George here? B: Is WHO here? A: George Sand. B: Ah, no."
    context := "B cannot ground the reference of 'George' and initiates clarification by Parameter Focussing; after B's clarification request the two gameboards differ in QUD and PENDING."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("ccur", "Parameter Focussing")]
    comment := "The gameboards after the second utterance are given in Ch. 6 (91)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_24a : LinguisticExample :=
  { id := "ginzburg2012_24a"
    source := ⟨"ginzburg-2012", "(24a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: Did Bo leave? B: Bo? A: Your cousin."
    discourseSegments := ["A: Did Bo leave?", "B: Bo?", "A: Your cousin."]
    glossedTokens := []
    translation := "A: Did Bo leave? B: Bo? A: Your cousin."
    context := "Other-initiated repair: a clarification request across utterances."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("repair", "other-initiated")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_24b : LinguisticExample :=
  { id := "ginzburg2012_24b"
    source := ⟨"ginzburg-2012", "(24b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: [Did Bo + {I mean} my cousin] leave?"
    discourseSegments := []
    glossedTokens := []
    translation := "A: Did Bo, I mean my cousin, leave?"
    context := "Self-initiated mid-utterance repair, the within-utterance analogue of (24a)."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("repair", "self-initiated")]
    comment := "Switchboard-style annotation: '+' marks the moment of interruption, '{}' the editing term."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_22a, ex_22b, ex_23a, ex_23b, ex_23c, ex_54, ex_65, ex_67, ex_78, ex_95, ch6_90, ex_24a, ex_24b]

end Ginzburg2012.Examples
