module

public import Linglib.Data.Examples.Schema

/-!
# `GroenendijkStokhof1984` — typed example data

Auto-generated from `Linglib/Data/Examples/GroenendijkStokhof1984.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace GroenendijkStokhof1984.Examples`.
-/

@[expose] public section

namespace GroenendijkStokhof1984.Examples

open Data.Examples

def gs1984_mentionsome_italian_newspaper : Datum :=
  { id := "gs1984_mentionsome_italian_newspaper"
    source := ⟨"groenendijk-stokhof-1984", "Ch. VI §5, p. 331"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Where can I buy an Italian newspaper?"
    glossedTokens := []
    context := "The questioner has a practical goal (getting an Italian newspaper); a single location suffices. Context determines whether the questioner wants all locations or just one."
    judgment := .acceptable
    alternatives := [("At the station kiosk", .acceptable)]
    readings := [("mention-some", .acceptable), ("mention-all", .acceptable)]
    paperFeatures := [("phenomenon", "mention_some")] }

def gs1984_mentionsome_know_newspaper : Datum :=
  { id := "gs1984_mentionsome_know_newspaper"
    source := ⟨"groenendijk-stokhof-1984", "Ch. VI §5.3, (9)-(10)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows where he can buy an Italian newspaper"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("mention-some", .acceptable), ("mention-all", .acceptable)]
    paperFeatures := [("phenomenon", "mention_some"), ("licensor", "know"), ("licenses_mention_some", "true")] }

def gs1984_mentionsome_wonder_newspaper : Datum :=
  { id := "gs1984_mentionsome_wonder_newspaper"
    source := ⟨"groenendijk-stokhof-1984", "Ch. VI §5.3, (11)-(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John wonders where he can buy an Italian newspaper"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("mention-some", .acceptable), ("mention-all", .acceptable)]
    paperFeatures := [("phenomenon", "mention_some"), ("licensor", "wonder"), ("licenses_mention_some", "true")] }

def gs1984_mentionsome_know_pen : Datum :=
  { id := "gs1984_mentionsome_know_pen"
    source := ⟨"groenendijk-stokhof-1984", "Ch. VI §5.3"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows who has a pen"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("mention-some", .acceptable), ("choice", .acceptable), ("mention-all", .acceptable)]
    paperFeatures := [("phenomenon", "mention_some"), ("licensor", "know"), ("licenses_mention_some", "true")] }

def gs1984_mentionsome_negative_pen : Datum :=
  { id := "gs1984_mentionsome_negative_pen"
    source := ⟨"groenendijk-stokhof-1984", "Ch. VI §5.2"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Where is a pen?"
    glossedTokens := []
    context := "The questioner needs a pen and wants a location where one can be found."
    judgment := .acceptable
    alternatives := [("In the study", .acceptable), ("Not in the drawer", .unacceptable), ("Nowhere / There isn't one", .acceptable)]
    readings := [("mention-some", .acceptable)]
    paperFeatures := [("phenomenon", "mention_some")] }

def gs1984_mentionsome_depends : Datum :=
  { id := "gs1984_mentionsome_depends"
    source := ⟨"groenendijk-stokhof-1984", "Ch. VI §5.4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It depends on who has a pen"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("mention-some", .unacceptable)]
    paperFeatures := [("phenomenon", "mention_some"), ("licensor", "depends"), ("licenses_mention_some", "false")] }

def gs1984_mentionsome_matter : Datum :=
  { id := "gs1984_mentionsome_matter"
    source := ⟨"groenendijk-stokhof-1984", "Ch. VI §5.4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It matters who has a pen"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("mention-some", .unacceptable)]
    paperFeatures := [("phenomenon", "mention_some"), ("licensor", "matter"), ("licenses_mention_some", "false")] }

def gs1984_mentionsome_determine : Datum :=
  { id := "gs1984_mentionsome_determine"
    source := ⟨"groenendijk-stokhof-1984", "Ch. VI §5.4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who gets the prize is determined by who wins"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("mention-some", .unacceptable)]
    paperFeatures := [("phenomenon", "mention_some"), ("licensor", "determine"), ("licenses_mention_some", "false")] }

def gs1984_mentionsome_know : Datum :=
  { id := "gs1984_mentionsome_know"
    source := ⟨"groenendijk-stokhof-1984", "Ch. VI §5.4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows who has a pen"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("mention-some", .acceptable)]
    paperFeatures := [("phenomenon", "mention_some"), ("licensor", "know"), ("licenses_mention_some", "true")] }

def gs1984_mentionsome_wonder : Datum :=
  { id := "gs1984_mentionsome_wonder"
    source := ⟨"groenendijk-stokhof-1984", "Ch. VI §5.4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John wonders who has a pen"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("mention-some", .acceptable)]
    paperFeatures := [("phenomenon", "mention_some"), ("licensor", "wonder"), ("licenses_mention_some", "true")] }

def gs1984_mentionsome_findout : Datum :=
  { id := "gs1984_mentionsome_findout"
    source := ⟨"groenendijk-stokhof-1984", "Ch. VI §5.4"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John found out who has a pen"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("mention-some", .acceptable)]
    paperFeatures := [("phenomenon", "mention_some"), ("licensor", "find out"), ("licenses_mention_some", "true")] }

def gs1984_mentiontwo_unicorns : Datum :=
  { id := "gs1984_mentiontwo_unicorns"
    source := ⟨"belnap-1982", "two-unicorns example"⟩
    reportedIn := some ⟨"groenendijk-stokhof-1984", "Ch. VI §5.3"⟩
    language := "stan1293"
    primaryText := "Where do two unicorns live?"
    glossedTokens := []
    context := "The cumulative reading is natural when the questioner wants to know the locations of the unicorns collectively."
    judgment := .acceptable
    alternatives := [("In the enchanted forest (where both unicorns live)", .acceptable), ("One in Paris, one in Rome", .acceptable), ("The white unicorn lives in Paris; the silver one in Rome", .acceptable)]
    readings := [("mention-some", .acceptable), ("cumulative", .acceptable), ("choice", .acceptable)]
    paperFeatures := [("phenomenon", "mention_some")] }

def gs1984_yourfather : Datum :=
  { id := "gs1984_yourfather"
    source := ⟨"groenendijk-stokhof-1984", "p. 359"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Whom did you talk to? Your father."
    glossedTokens := []
    context := "The questioner knows who their father is."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "pragmatic_answerhood"), ("rigidity", "pragmatic_not_semantic")] }

def gs1984_zoetemelk_rigid : Datum :=
  { id := "gs1984_zoetemelk_rigid"
    source := ⟨"groenendijk-stokhof-1984", "p. 359"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who won the Tour de France in 1980? The one who ended second in 1979."
    glossedTokens := []
    context := "The questioner knows Joop Zoetemelk ended second in 1979."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "pragmatic_answerhood"), ("rigidity", "pragmatic_not_semantic")] }

def gs1984_zoetemelk_false_true : Datum :=
  { id := "gs1984_zoetemelk_false_true"
    source := ⟨"groenendijk-stokhof-1984", "p. 360"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who won the Tour de France in 1980? The one who won in 1979."
    glossedTokens := []
    context := "The questioner wrongly believes Joop Zoetemelk won in 1979."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "pragmatic_answerhood"), ("answer_truth", "false_but_conveys_true")] }

def gs1984_elderly_lady_bootshop : Datum :=
  { id := "gs1984_elderly_lady_bootshop"
    source := ⟨"groenendijk-stokhof-1984", "pp. 360-361"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who served you when you bought these boots? An elderly lady wearing glasses."
    glossedTokens := []
    context := "A customer bought boots; the sales manager wants to know who served them. The manager knows all staff members well but not who served this customer; the customer doesn't know staff names and can only give a physical description. Only one elderly lady with glasses is on the staff."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "pragmatic_answerhood"), ("rigidity", "pragmatically_definite")] }

def gs1984_profa_contribution : Datum :=
  { id := "gs1984_profa_contribution"
    source := ⟨"groenendijk-stokhof-1984", "p. 362"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "From which authors did the editors already receive their contribution? At least from Prof. A."
    glossedTokens := []
    context := "Prof. A. is always the last to send in contributions."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "pragmatic_answerhood"), ("exhaustive_inference", "true")] }

def gs1984_profa_acceptance : Datum :=
  { id := "gs1984_profa_acceptance"
    source := ⟨"groenendijk-stokhof-1984", "p. 362"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "From whom did the organizers receive a letter of acceptance? At least from Prof. A."
    glossedTokens := []
    context := "Prof. A. is always the first to accept invitations."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "pragmatic_answerhood"), ("exhaustive_inference", "false")] }

def gs1984_court_testimony : Datum :=
  { id := "gs1984_court_testimony"
    source := ⟨"groenendijk-stokhof-1984", "pp. 363, 390"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John Smith of 123 Main Street"
    glossedTokens := []
    context := "Court of Law testimony: questions are posed on behalf of the social community, so answers must work for a great variety of information sets."
    judgment := .acceptable
    alternatives := [("Your neighbor's husband", .unacceptable)]
    readings := []
    paperFeatures := [("phenomenon", "pragmatic_answerhood"), ("rigidity", "semantic_required")] }

def gs1984_pairlist_each_professor : Datum :=
  { id := "gs1984_pairlist_each_professor"
    source := ⟨"groenendijk-stokhof-1984", "Ch. VI §2.1, p. 403"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which student was recommended by each professor?"
    glossedTokens := []
    context := "Faculty meeting about graduate admissions."
    judgment := .acceptable
    alternatives := [("Prof. Smith recommended Alice, Prof. Jones recommended Bob, Prof. Brown recommended Carol", .acceptable), ("Alice (was recommended by all professors)", .acceptable)]
    readings := [("pair-list", .acceptable), ("single", .acceptable)]
    paperFeatures := [("phenomenon", "pair_list"), ("quantifier", "each"), ("embedding", "matrix"), ("pair_list_ok", "true")] }

def gs1984_pairlist_every_man : Datum :=
  { id := "gs1984_pairlist_every_man"
    source := ⟨"groenendijk-stokhof-1984", "Ch. VI §2.1, p. 404"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Who does every man love?"
    glossedTokens := []
    context := "Discussion about romantic relationships in a small community."
    judgment := .acceptable
    alternatives := [("John loves Mary, Bill loves Sue, Tom loves Alice", .acceptable), ("Mary (is loved by all men)", .acceptable)]
    readings := [("pair-list", .acceptable), ("single", .acceptable)]
    paperFeatures := [("phenomenon", "pair_list"), ("quantifier", "every"), ("embedding", "matrix"), ("pair_list_ok", "true")] }

def gs1984_functional_his_teachers : Datum :=
  { id := "gs1984_functional_his_teachers"
    source := ⟨"groenendijk-stokhof-1984", "Ch. VI §2.1, p. 405"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which of his teachers does every student admire?"
    glossedTokens := []
    context := "Survey about student-teacher relationships."
    judgment := .acceptable
    alternatives := [("John admires Prof. Smith, Mary admires Prof. Jones, Bill admires Prof. Brown", .acceptable)]
    readings := [("functional pair-list", .acceptable), ("single", .unacceptable)]
    paperFeatures := [("phenomenon", "pair_list"), ("quantifier", "every"), ("embedding", "matrix"), ("pair_list_ok", "true")] }

def gs1984_pairlist_know : Datum :=
  { id := "gs1984_pairlist_know"
    source := ⟨"groenendijk-stokhof-1984", "Ch. VI §2.1, p. 408"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows which student each professor recommended"
    glossedTokens := []
    context := "Embedded under 'know'."
    judgment := .acceptable
    alternatives := [("John knows: Smith recommended Alice, Jones recommended Bob, Brown recommended Carol", .acceptable), ("John knows: Alice (recommended by all)", .acceptable)]
    readings := [("pair-list", .acceptable), ("single", .acceptable)]
    paperFeatures := [("phenomenon", "pair_list"), ("quantifier", "each"), ("embedding", "know"), ("pair_list_ok", "true")] }

def gs1984_pairlist_wonder : Datum :=
  { id := "gs1984_pairlist_wonder"
    source := ⟨"groenendijk-stokhof-1984", "Ch. VI §2.1, p. 409"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John wonders which student each professor recommended"
    glossedTokens := []
    context := "Embedded under 'wonder'."
    judgment := .acceptable
    alternatives := [("John wonders whether there's a student all recommended", .acceptable)]
    readings := [("pair-list", .marginal), ("single", .acceptable)]
    paperFeatures := [("phenomenon", "pair_list"), ("quantifier", "each"), ("embedding", "wonder"), ("pair_list_ok", "false")] }

def gs1984_choice_john_or_mary : Datum :=
  { id := "gs1984_choice_john_or_mary"
    source := ⟨"groenendijk-stokhof-1984", "Ch. VI §2.2, p. 411"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Whom does John or Mary love?"
    glossedTokens := []
    context := "Discussing potential matches in a group."
    judgment := .acceptable
    alternatives := [("If John: Bill. If Mary: Sue.", .acceptable), ("Bill and Sue (loved by John-or-Mary collectively)", .acceptable)]
    readings := [("choice", .acceptable), ("non-choice", .acceptable)]
    paperFeatures := [("phenomenon", "choice"), ("quantifier", "disjunction"), ("embedding", "matrix")] }

def gs1984_choice_know_mary_or_sue : Datum :=
  { id := "gs1984_choice_know_mary_or_sue"
    source := ⟨"groenendijk-stokhof-1984", "Ch. VI §2.2, p. 412"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John knows whom Mary or Sue invited"
    glossedTokens := []
    context := "Embedded under 'know'."
    judgment := .acceptable
    alternatives := [("John knows: If Mary invited: Bill. If Sue invited: Tom.", .acceptable), ("John knows who was invited by at least one of them", .acceptable)]
    readings := [("choice", .acceptable), ("non-choice", .acceptable)]
    paperFeatures := [("phenomenon", "choice"), ("quantifier", "disjunction"), ("embedding", "know")] }

def gs1984_choice_some_professor : Datum :=
  { id := "gs1984_choice_some_professor"
    source := ⟨"groenendijk-stokhof-1984", "Ch. VI §2.2, p. 413"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Which student does some professor recommend?"
    glossedTokens := []
    context := "Asking about recommendations."
    judgment := .acceptable
    alternatives := [("Prof. Smith recommends Alice; that's the relevant answer", .acceptable), ("Alice, Bob, and Carol are each recommended by at least one professor", .acceptable)]
    readings := [("choice", .acceptable), ("non-choice", .acceptable)]
    paperFeatures := [("phenomenon", "choice"), ("quantifier", "some"), ("embedding", "matrix")] }

def all : List Datum := [gs1984_mentionsome_italian_newspaper, gs1984_mentionsome_know_newspaper, gs1984_mentionsome_wonder_newspaper, gs1984_mentionsome_know_pen, gs1984_mentionsome_negative_pen, gs1984_mentionsome_depends, gs1984_mentionsome_matter, gs1984_mentionsome_determine, gs1984_mentionsome_know, gs1984_mentionsome_wonder, gs1984_mentionsome_findout, gs1984_mentiontwo_unicorns, gs1984_yourfather, gs1984_zoetemelk_rigid, gs1984_zoetemelk_false_true, gs1984_elderly_lady_bootshop, gs1984_profa_contribution, gs1984_profa_acceptance, gs1984_court_testimony, gs1984_pairlist_each_professor, gs1984_pairlist_every_man, gs1984_functional_his_teachers, gs1984_pairlist_know, gs1984_pairlist_wonder, gs1984_choice_john_or_mary, gs1984_choice_know_mary_or_sue, gs1984_choice_some_professor]

end GroenendijkStokhof1984.Examples
