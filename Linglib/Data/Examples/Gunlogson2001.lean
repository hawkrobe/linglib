import Linglib.Data.Examples.Schema

/-!
# `Gunlogson2001` — typed example data

Auto-generated from `Linglib/Data/Examples/Gunlogson2001.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Gunlogson2001.Examples`.
-/

namespace Gunlogson2001.Examples

open Data.Examples

def ex_13 : LinguisticExample :=
  { id := "gunlogson2001_13"
    source := ⟨"gunlogson-2001", "(13)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "During the tax year, did you receive a distribution from a foreign trust?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "On a tax form."
    judgment := .acceptable
    alternatives := [("During the tax year, you received a distribution from a foreign trust?", .unacceptable), ("During the tax year, you received a distribution from a foreign trust.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "neutrality"), ("locutions", "interrogative;risingDeclarative;fallingDeclarative")]
    comment := "Declaratives cannot elicit information in an unbiased way."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_14 : LinguisticExample :=
  { id := "gunlogson2001_14"
    source := ⟨"gunlogson-2001", "(14)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is it bigger than a breadbox?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "In a guessing game."
    judgment := .acceptable
    alternatives := [("It's bigger than a breadbox?", .unacceptable), ("It's bigger than a breadbox.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "neutrality"), ("locutions", "interrogative;risingDeclarative;fallingDeclarative")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_16 : LinguisticExample :=
  { id := "gunlogson2001_16"
    source := ⟨"gunlogson-2001", "(16)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Did she lie to the grand jury?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "It's an open question."
    judgment := .acceptable
    alternatives := [("She lied to the grand jury?", .unacceptable), ("She lied to the grand jury.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "neutrality"), ("locutions", "interrogative;risingDeclarative;fallingDeclarative")]
    comment := "The issue raised by a declarative question cannot be regarded as open."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_27 : LinguisticExample :=
  { id := "gunlogson2001_27"
    source := ⟨"gunlogson-2001", "(27)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Can you (please) pass the salt?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := [("You can (please) pass the salt?", .unacceptable), ("You can (please) pass the salt.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "neutrality"), ("locutions", "interrogative;risingDeclarative;fallingDeclarative")]
    comment := "Polite requests for action are a function of interrogatives that declaratives lack."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_31 : LinguisticExample :=
  { id := "gunlogson2001_31"
    source := ⟨"gunlogson-2001", "(31)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Am I from Skokie?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Radio station DJ: Good morning Susan. Where are you calling from? The caller answers."
    judgment := .unacceptable
    alternatives := [("I'm from Skokie?", .acceptable), ("I'm from Skokie.", .acceptable)]
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "informativeRising"), ("locutions", "interrogative;risingDeclarative;fallingDeclarative")]
    comment := "A rising declarative can offer new information; adapted by the paper from Hirschberg and Ward 1995. Rising interrogatives lack this function."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_33 : LinguisticExample :=
  { id := "gunlogson2001_33"
    source := ⟨"gunlogson-2001", "(33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Has the manager of course been informed?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .unacceptable
    alternatives := [("The manager has of course been informed?", .acceptable), ("The manager has of course been informed.", .acceptable)]
    readings := []
    paperFeatures := [("section", "2.2"), ("phenomenon", "biasMarker"), ("locutions", "interrogative;risingDeclarative;fallingDeclarative")]
    comment := "Bias markers such as 'of course' are incompatible with interrogatives, an observation the paper credits to Huddleston 1994."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_44 : LinguisticExample :=
  { id := "gunlogson2001_44"
    source := ⟨"gunlogson-2001", "(44)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Has it? I don't see much evidence of that."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "A and B are looking at a co-worker's much-dented car. A: His driving has gotten a lot better. B responds."
    judgment := .acceptable
    alternatives := [("It has? I don't see much evidence of that.", .acceptable), ("It has. I don't see much evidence of that.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "2.3"), ("phenomenon", "speakerCommitment"), ("locutions", "interrogative;risingDeclarative;fallingDeclarative")]
    comment := "Only the falling declarative is inconsistent with the skeptical follow-up."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_45 : LinguisticExample :=
  { id := "gunlogson2001_45"
    source := ⟨"gunlogson-2001", "(45)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is it? Thanks, I'll use a different one."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "A: That copier is broken. B responds."
    judgment := .acceptable
    alternatives := [("It is? Thanks, I'll use a different one.", .acceptable), ("(Oh), it is. Thanks, I'll use a different one.", .acceptable)]
    readings := []
    paperFeatures := [("section", "2.3"), ("phenomenon", "speakerCommitment"), ("locutions", "interrogative;risingDeclarative;fallingDeclarative")]
    comment := "All three are compatible with the speaker's routine acceptance; a reiterative question."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_46 : LinguisticExample :=
  { id := "gunlogson2001_46"
    source := ⟨"gunlogson-2001", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is Jake here? Then let's get started."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "A: Jake's here. B responds."
    judgment := .acceptable
    alternatives := [("Jake's here? Then let's get started.", .acceptable), ("(Oh), Jake's here. Then let's get started.", .acceptable)]
    readings := []
    paperFeatures := [("section", "2.3"), ("phenomenon", "speakerCommitment"), ("locutions", "interrogative;risingDeclarative;fallingDeclarative")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_47 : LinguisticExample :=
  { id := "gunlogson2001_47"
    source := ⟨"gunlogson-2001", "(47)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is France a monarchy?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "A: The king of France is bald. B responds."
    judgment := .acceptable
    alternatives := [("France is a monarchy?", .acceptable), ("France is a monarchy.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "2.3"), ("phenomenon", "speakerCommitment"), ("locutions", "interrogative;risingDeclarative;fallingDeclarative")]
    comment := "The question concerns a presupposition of A's utterance rather than its main content."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_48 : LinguisticExample :=
  { id := "gunlogson2001_48"
    source := ⟨"gunlogson-2001", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is shoplifting fun?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Uttered to insinuate that the addressee has shoplifted."
    judgment := .acceptable
    alternatives := [("Shoplifting's fun?", .acceptable), ("Shoplifting's fun.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "2.3"), ("phenomenon", "speakerCommitment"), ("locutions", "interrogative;risingDeclarative;fallingDeclarative")]
    comment := "The falling declarative portrays the speaker as the source of the information."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_100 : LinguisticExample :=
  { id := "gunlogson2001_100"
    source := ⟨"gunlogson-2001", "(100)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A: That was a kingfisher. B: Are you sure? It looked like a seagull to me. A: I'm positive. It was a kingfisher."
    discourseSegments := ["A: That was a kingfisher.", "B: Are you sure? It looked like a seagull to me.", "A: I'm positive. It was a kingfisher."]
    glossedTokens := []
    translation := ""
    context := "A is watching a bird fly away; neither A nor B has a prior commitment about its identity."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3.5"), ("phenomenon", "entailedButInformative")]
    comment := "A's second falling declarative is entailed by the context, since A is already committed, but still informative with respect to B's commitment set."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_102 : LinguisticExample :=
  { id := "gunlogson2001_102"
    source := ⟨"gunlogson-2001", "(102)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Are we out of beer?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "A: I've just searched the refrigerator and there's absolutely nothing cold to drink. B responds."
    judgment := .acceptable
    alternatives := [("We're out of beer?", .acceptable), ("(So) we're out of beer.", .acceptable)]
    readings := []
    paperFeatures := [("section", "3.5"), ("phenomenon", "vacuousness"), ("locutions", "interrogative;risingDeclarative;fallingDeclarative")]
    comment := "Not vacuous: A's entailment that there is no beer is not yet a joint commitment, though the rising declarative and the interrogative are uninformative and entailed."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_103 : LinguisticExample :=
  { id := "gunlogson2001_103"
    source := ⟨"gunlogson-2001", "(103)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Are we out of beer?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "B: I've just searched the refrigerator and there's absolutely nothing cold to drink. A: Yeah, I know. We're out of just about everything. B responds."
    judgment := .unacceptable
    alternatives := [("We're out of beer?", .unacceptable), ("(So) we're out of beer.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "3.5"), ("phenomenon", "vacuousness"), ("locutions", "interrogative;risingDeclarative;fallingDeclarative")]
    comment := "Vacuous in every form: A and B agree about the barren state of the refrigerator."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_118 : LinguisticExample :=
  { id := "gunlogson2001_118"
    source := ⟨"gunlogson-2001", "(118)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is Maria married?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "A: Maria's husband was at the party. B responds."
    judgment := .acceptable
    alternatives := [("Maria's married?", .acceptable), ("Maria's married.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.3"), ("phenomenon", "fallingDeclarativeQuestion"), ("locutions", "interrogative;risingDeclarative;fallingDeclarative")]
    comment := "The falling declarative fails as a question although A's statement presupposes its content."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_128 : LinguisticExample :=
  { id := "gunlogson2001_128"
    source := ⟨"gunlogson-2001", "(128)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Is it raining?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Robin is sitting in a windowless computer room when another person enters, wearing a wet raincoat and boots. Robin says:"
    judgment := .acceptable
    alternatives := [("It's raining?", .acceptable), ("(I see that/So) It's raining.", .acceptable)]
    readings := []
    paperFeatures := [("section", "4.3"), ("phenomenon", "fallingDeclarativeQuestion"), ("locutions", "interrogative;risingDeclarative;fallingDeclarative")]
    comment := "A resolving question; the falling declarative works much better with the parenthesized inferential marker, which shows the speaker's commitment to be contingent on the addressee's."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_13, ex_14, ex_16, ex_27, ex_31, ex_33, ex_44, ex_45, ex_46, ex_47, ex_48, ex_100, ex_102, ex_103, ex_118, ex_128]

end Gunlogson2001.Examples
