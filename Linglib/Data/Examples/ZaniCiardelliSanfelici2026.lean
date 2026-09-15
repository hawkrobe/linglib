import Linglib.Data.Examples.Schema

/-!
# `ZaniCiardelliSanfelici2026` — typed example data

Auto-generated from `Linglib/Data/Examples/ZaniCiardelliSanfelici2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace ZaniCiardelliSanfelici2026.Examples`.
-/

namespace ZaniCiardelliSanfelici2026.Examples

open Data.Examples

def ex_1a : LinguisticExample :=
  { id := "zaniciardellisanfelici2026_1a"
    source := ⟨"zani-ciardelli-sanfelici-2026", "(1a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If it rains or snows, the hike will be cancelled."
    discourseSegments := []
    glossedTokens := []
    translation := "If it rains or snows, the hike will be cancelled."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "indicative"), ("reading", "SDA")]
    comment := "Intuitively equivalent to the conjunction of its simplifications, (2a)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_1b : LinguisticExample :=
  { id := "zaniciardellisanfelici2026_1b"
    source := ⟨"zani-ciardelli-sanfelici-2026", "(1b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If it had rained or snowed, the hike would have been cancelled."
    discourseSegments := []
    glossedTokens := []
    translation := "If it had rained or snowed, the hike would have been cancelled."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "counterfactual"), ("reading", "SDA")]
    comment := "Intuitively equivalent to the conjunction of its simplifications, (2b)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_3 : LinguisticExample :=
  { id := "zaniciardellisanfelici2026_3"
    source := ⟨"zani-ciardelli-sanfelici-2026", "(3)"⟩
    reportedIn := some ⟨"mckay-vaninwagen-1977", ""⟩
    language := "stan1293"
    primaryText := "If Spain had fought either with the Axis or with the Allies in World War II, it would have fought with the Axis."
    discourseSegments := []
    glossedTokens := []
    translation := "If Spain had fought either with the Axis or with the Allies in World War II, it would have fought with the Axis."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "counterfactual"), ("reading", "AR"), ("type", "specificational")]
    comment := "Cited from McKay and van Inwagen (1977): true because fighting with the Axis is the more realistic disjunct, so SDA fails."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_4 : LinguisticExample :=
  { id := "zaniciardellisanfelici2026_4"
    source := ⟨"zani-ciardelli-sanfelici-2026", "(4)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If we had had good weather or the sun had grown cold, we would have had a bumper crop."
    discourseSegments := []
    glossedTokens := []
    translation := "If we had had good weather or the sun had grown cold, we would have had a bumper crop."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "counterfactual"), ("reading", "SDA")]
    comment := "Nute's bumper-crop example: judged false because the simplification with the less realistic disjunct, (4b), is false, against Lewis's prediction."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_6 : LinguisticExample :=
  { id := "zaniciardellisanfelici2026_6"
    source := ⟨"zani-ciardelli-sanfelici-2026", "(6)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "If you press the red button or the blue button, the machine will explode. But I don't remember which."
    discourseSegments := []
    glossedTokens := []
    translation := "If you press the red button or the blue button, the machine will explode. But I don't remember which."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "indicative"), ("reading", "DCR")]
    comment := "The continuation forces the disjunctive conditional reading: the disjunction of the simplifications."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_7 : LinguisticExample :=
  { id := "zaniciardellisanfelici2026_7"
    source := ⟨"zani-ciardelli-sanfelici-2026", "(7)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "You may have cake or ice-cream."
    discourseSegments := []
    glossedTokens := []
    translation := "You may have cake or ice-cream."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("inference", "free choice")]
    comment := "Free-choice inference to each permission, taken to share its source with SDA."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_8 : LinguisticExample :=
  { id := "zaniciardellisanfelici2026_8"
    source := ⟨"zani-ciardelli-sanfelici-2026", "(8)"⟩
    reportedIn := some ⟨"tieu-kriz-chemla-2019", ""⟩
    language := "stan1293"
    primaryText := "The circles are red."
    discourseSegments := []
    glossedTokens := []
    translation := "The circles are red."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("phenomenon", "plural definite homogeneity")]
    comment := "Adults require all circles red; about a third of 4- and 5-year-olds accept it once some circles are red (Tieu et al. 2019)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def target_ind : LinguisticExample :=
  { id := "zaniciardellisanfelici2026_target_ind"
    source := ⟨"zani-ciardelli-sanfelici-2026", "§4 target item, Ind."⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Se lo scoiattolo o la tartaruga vincerà la gara, avrà in premio una nocciola."
    discourseSegments := []
    glossedTokens := [("Se", "if"), ("lo", "the"), ("scoiattolo", "squirrel"), ("o", "or"), ("la", "the"), ("tartaruga", "tortoise"), ("vincerà", "win.FUT.3SG"), ("la", "the"), ("gara", "race"), ("avrà", "get.FUT.3SG"), ("in", "as"), ("premio", "prize"), ("una", "a"), ("nocciola", "hazelnut")]
    translation := "If the squirrel or the tortoise wins the race, it will get a hazelnut."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "indicative"), ("item", "target"), ("schema", "(9a)")]
    comment := "Target item: the hazelnut is the squirrel's prize, so one simplification is true and the other false."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def target_ctf : LinguisticExample :=
  { id := "zaniciardellisanfelici2026_target_ctf"
    source := ⟨"zani-ciardelli-sanfelici-2026", "§4 target item, Ctf."⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Se lo scoiattolo o la tartaruga avesse vinto la gara, avrebbe avuto in premio una nocciola."
    discourseSegments := []
    glossedTokens := [("Se", "if"), ("lo", "the"), ("scoiattolo", "squirrel"), ("o", "or"), ("la", "the"), ("tartaruga", "tortoise"), ("avesse", "have.SBJV.IPFV.3SG"), ("vinto", "win.PTCP.PST"), ("la", "the"), ("gara", "race"), ("avrebbe", "have.COND.3SG"), ("avuto", "get.PTCP.PST"), ("in", "as"), ("premio", "prize"), ("una", "a"), ("nocciola", "hazelnut")]
    translation := "If the squirrel or the tortoise had won the race, it would have got a hazelnut."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "counterfactual"), ("item", "target"), ("schema", "(9a)")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def control_ind : LinguisticExample :=
  { id := "zaniciardellisanfelici2026_control_ind"
    source := ⟨"zani-ciardelli-sanfelici-2026", "§4 control item, Ind."⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Se lo scoiattolo vincerà la gara, avrà in premio una nocciola."
    discourseSegments := []
    glossedTokens := [("Se", "if"), ("lo", "the"), ("scoiattolo", "squirrel"), ("vincerà", "win.FUT.3SG"), ("la", "the"), ("gara", "race"), ("avrà", "get.FUT.3SG"), ("in", "as"), ("premio", "prize"), ("una", "a"), ("nocciola", "hazelnut")]
    translation := "If the squirrel wins the race, it will get a hazelnut."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "indicative"), ("item", "control"), ("expected", "true")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def control_ctf : LinguisticExample :=
  { id := "zaniciardellisanfelici2026_control_ctf"
    source := ⟨"zani-ciardelli-sanfelici-2026", "§4 control item, Ctf."⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Se lo scoiattolo avesse vinto la gara, avrebbe avuto in premio una nocciola."
    discourseSegments := []
    glossedTokens := [("Se", "if"), ("lo", "the"), ("scoiattolo", "squirrel"), ("avesse", "have.SBJV.IPFV.3SG"), ("vinto", "win.PTCP.PST"), ("la", "the"), ("gara", "race"), ("avrebbe", "have.COND.3SG"), ("avuto", "get.PTCP.PST"), ("in", "as"), ("premio", "prize"), ("una", "a"), ("nocciola", "hazelnut")]
    translation := "If the squirrel had won the race, it would have got a hazelnut."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "counterfactual"), ("item", "control"), ("expected", "true")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def closeness_ind : LinguisticExample :=
  { id := "zaniciardellisanfelici2026_closeness_ind"
    source := ⟨"zani-ciardelli-sanfelici-2026", "§4 closeness evaluation item, Ind."⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Se non vincerà la lepre, vincerà lo scoiattolo."
    discourseSegments := []
    glossedTokens := [("Se", "if"), ("non", "NEG"), ("vincerà", "win.FUT.3SG"), ("la", "the"), ("lepre", "hare"), ("vincerà", "win.FUT.3SG"), ("lo", "the"), ("scoiattolo", "squirrel")]
    translation := "If the hare doesn't win, the squirrel will win."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "indicative"), ("item", "closeness evaluation")]
    comment := "Acceptance reveals that the participant regards the squirrel as a more realistic winner than the tortoise."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def closeness_ctf : LinguisticExample :=
  { id := "zaniciardellisanfelici2026_closeness_ctf"
    source := ⟨"zani-ciardelli-sanfelici-2026", "§4 closeness evaluation item, Ctf."⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Se non avesse vinto la lepre, avrebbe vinto lo scoiattolo."
    discourseSegments := []
    glossedTokens := [("Se", "if"), ("non", "NEG"), ("avesse", "have.SBJV.IPFV.3SG"), ("vinto", "win.PTCP.PST"), ("la", "the"), ("lepre", "hare"), ("avrebbe", "have.COND.3SG"), ("vinto", "win.PTCP.PST"), ("lo", "the"), ("scoiattolo", "squirrel")]
    translation := "If the hare hadn't won, the squirrel would have won."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "counterfactual"), ("item", "closeness evaluation")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def app_1 : LinguisticExample :=
  { id := "zaniciardellisanfelici2026_app_1"
    source := ⟨"zani-ciardelli-sanfelici-2026", "Appendix (1)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Se il tasto rosso o il tasto blu viene premuto, il computer esplode. Non mi ricordo quale dei due."
    discourseSegments := []
    glossedTokens := [("Se", "if"), ("il", "the"), ("tasto", "key"), ("rosso", "red"), ("o", "or"), ("il", "the"), ("tasto", "key"), ("blu", "blue"), ("viene", "come.3SG"), ("premuto", "pressed.PTCP.SG"), ("il", "the"), ("computer", "computer"), ("esplode", "explodes.3SG"), ("Non", "not"), ("mi", "CL.1SG"), ("ricordo", "remember.1SG"), ("quale", "which"), ("dei", "of.the"), ("due", "two")]
    translation := "If the red key or the blue key is pressed, the computer explodes. I don't remember which one."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("agreement", "singular"), ("reading", "DCR")]
    comment := "Singular agreement with the disjunctive subject allows the ignorance continuation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def app_2 : LinguisticExample :=
  { id := "zaniciardellisanfelici2026_app_2"
    source := ⟨"zani-ciardelli-sanfelici-2026", "Appendix (2)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Se il tasto rosso o il tasto blu vengono premuti, il computer esplode. Non mi ricordo quale dei due."
    discourseSegments := []
    glossedTokens := [("Se", "if"), ("il", "the"), ("tasto", "key"), ("rosso", "red"), ("o", "or"), ("il", "the"), ("tasto", "key"), ("blu", "blue"), ("vengono", "come.3PL"), ("premuti", "pressed.PTCP.PL"), ("il", "the"), ("computer", "computer"), ("esplode", "explodes.3SG"), ("Non", "not"), ("mi", "CL.1SG"), ("ricordo", "remember.1SG"), ("quale", "which"), ("dei", "of.the"), ("due", "two")]
    translation := "If the red key or the blue key are pressed, the computer explodes. I don't remember which one."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("agreement", "plural"), ("reading", "DCR")]
    comment := "Plural agreement blocks the ignorance continuation, marked # in the paper."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1a, ex_1b, ex_3, ex_4, ex_6, ex_7, ex_8, target_ind, target_ctf, control_ind, control_ctf, closeness_ind, closeness_ctf, app_1, app_2]

end ZaniCiardelliSanfelici2026.Examples
