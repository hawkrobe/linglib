import Linglib.Data.Examples.Schema

/-!
# `FuscoSgrizzi2026` — typed example data

Auto-generated from `Linglib/Data/Examples/FuscoSgrizzi2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace FuscoSgrizzi2026.Examples`.
-/

namespace FuscoSgrizzi2026.Examples

open Data.Examples

def ex4a : LinguisticExample :=
  { id := "fuscosgrizzi2026_ex4a"
    source := ⟨"fusco-sgrizzi-2026", "(4a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Marco ha convinto Gianni di avere un figlio."
    discourseSegments := []
    glossedTokens := [("Marco", "Marco"), ("ha", "have-PRS.3SG"), ("convinto", "convince-PST.PTCP"), ("Gianni", "Gianni"), ("di", "di"), ("avere", "have-INF"), ("un", "a"), ("figlio.", "child")]
    translation := "Marco has convinced Gianni that he has a child."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("size", "cP"), ("diagnostic", "belief"), ("grammatical", "yes")]
    comment := "The belief reading: Marco causes Gianni to believe a state of affairs. PRO may be Marco or Gianni."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4b : LinguisticExample :=
  { id := "fuscosgrizzi2026_ex4b"
    source := ⟨"fusco-sgrizzi-2026", "(4b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Marco ha convinto Gianni a avere un figlio."
    discourseSegments := []
    glossedTokens := [("Marco", "Marco"), ("ha", "have-PRS.3SG"), ("convinto", "convince-PST.PTCP"), ("Gianni", "Gianni"), ("a", "a"), ("avere", "have-INF"), ("un", "a"), ("figlio.", "child")]
    translation := "Marco has convinced Gianni to have a child."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("size", "aP"), ("diagnostic", "intention"), ("grammatical", "yes")]
    comment := "The intention reading: Gianni comes to intend to bring the state of affairs about; at the time of the convincing he does not yet have a child."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4a_control : LinguisticExample :=
  { id := "fuscosgrizzi2026_ex4a_control"
    source := ⟨"fusco-sgrizzi-2026", "(4a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Marco ha convinto Gianni di avere un figlio."
    discourseSegments := []
    glossedTokens := [("Marco", "Marco"), ("ha", "have-PRS.3SG"), ("convinto", "convince-PST.PTCP"), ("Gianni", "Gianni"), ("di", "di"), ("avere", "have-INF"), ("un", "a"), ("figlio.", "child")]
    translation := "Marco has convinced Gianni that he (Marco or Gianni) has a child."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("size", "cP"), ("diagnostic", "subjectControl"), ("grammatical", "yes")]
    comment := "The di-infinitive allows subject as well as object control: FinP hosts the logophoric centre."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4b_control : LinguisticExample :=
  { id := "fuscosgrizzi2026_ex4b_control"
    source := ⟨"fusco-sgrizzi-2026", "(4b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Marco ha convinto Gianni a avere un figlio."
    discourseSegments := []
    glossedTokens := [("Marco", "Marco"), ("ha", "have-PRS.3SG"), ("convinto", "convince-PST.PTCP"), ("Gianni", "Gianni"), ("a", "a"), ("avere", "have-INF"), ("un", "a"), ("figlio.", "child")]
    translation := "Marco has convinced Gianni that Marco will have a child."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("size", "aP"), ("diagnostic", "subjectControl"), ("grammatical", "no")]
    comment := "The a-infinitive allows only object control: the matrix object is the closest referent for PRO. Footnote 1 reports a marginal subject-control reading for a causative complement."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex11a : LinguisticExample :=
  { id := "fuscosgrizzi2026_ex11a"
    source := ⟨"fusco-sgrizzi-2026", "(11a)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Marco ha convinto Gianni di avere un figlio, ma non è vero."
    discourseSegments := []
    glossedTokens := [("Marco", "Marco"), ("ha", "have-PRS.3SG"), ("convinto", "convince-PST.PTCP"), ("Gianni", "Gianni"), ("di", "di"), ("avere", "have-INF"), ("un", "a"), ("figlio,", "child"), ("ma", "but"), ("non", "not"), ("è", "be-PRS.3SG"), ("vero.", "true")]
    translation := "Marco has convinced Gianni that he has a child, but it is not true."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("size", "cP"), ("diagnostic", "truthAssessable"), ("grammatical", "yes")]
    comment := "A propositional complement can be assessed for truth."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex11b : LinguisticExample :=
  { id := "fuscosgrizzi2026_ex11b"
    source := ⟨"fusco-sgrizzi-2026", "(11b)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Marco ha convinto Gianni ad avere un figlio, ma non è vero."
    discourseSegments := []
    glossedTokens := [("Marco", "Marco"), ("ha", "have-PRS.3SG"), ("convinto", "convince-PST.PTCP"), ("Gianni", "Gianni"), ("ad", "a"), ("avere", "have-INF"), ("un", "a"), ("figlio,", "child"), ("ma", "but"), ("non", "not"), ("è", "be-PRS.3SG"), ("vero.", "true")]
    translation := "Marco has convinced Gianni to have a child, but it is not true."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("size", "aP"), ("diagnostic", "truthAssessable"), ("grammatical", "no")]
    comment := "The a-infinitive is not large enough to be a proposition; the continuation is infelicitous."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex12 : LinguisticExample :=
  { id := "fuscosgrizzi2026_ex12"
    source := ⟨"fusco-sgrizzi-2026", "(12)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "La conduttrice ha convinto l'ospite ad essere intervistato."
    discourseSegments := []
    glossedTokens := [("La", "the"), ("conduttrice", "conductor"), ("ha", "have-PRS.3SG"), ("convinto", "convince-PST.PTCP"), ("l'ospite", "the.guest"), ("ad", "a"), ("essere", "be-INF"), ("intervistato.", "interviewed-PST.PTCP.M")]
    translation := "The conductor has convinced the guest to be interviewed."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("size", "aP"), ("diagnostic", "passive"), ("grammatical", "yes")]
    comment := "Passive is available in the a-infinitive; the guest consents to the interview."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex13 : LinguisticExample :=
  { id := "fuscosgrizzi2026_ex13"
    source := ⟨"fusco-sgrizzi-2026", "(13)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Marco ha convinto Gianni a cominciare a lavorare."
    discourseSegments := []
    glossedTokens := [("Marco", "Marco"), ("ha", "have-PRS.3SG"), ("convinto", "convince-PST.PTCP"), ("Gianni", "Gianni"), ("a", "a"), ("cominciare", "begin-INF"), ("a", "to"), ("lavorare.", "work-INF")]
    translation := "Marco has convinced Gianni to start working."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("size", "aP"), ("diagnostic", "aspectual"), ("grammatical", "yes")]
    comment := "Low aspectual restructuring verbs, merged at the edge of vP, fit inside the a-infinitive; the paper also gives continuare a and finire di."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex14 : LinguisticExample :=
  { id := "fuscosgrizzi2026_ex14"
    source := ⟨"fusco-sgrizzi-2026", "(14)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "L'operaio lo prova a costruire."
    discourseSegments := []
    glossedTokens := [("L'operaio", "the-worker"), ("lo", "it"), ("prova", "try-PRS.3SG"), ("a", "to"), ("costruire.", "build")]
    translation := "The worker tries to build it."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("size", "vP"), ("diagnostic", "cliticClimbing"), ("grammatical", "yes")]
    comment := "Under the restructuring verb provare the object clitic climbs over the matrix verb: the infinitive is no larger than vP."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex15 : LinguisticExample :=
  { id := "fuscosgrizzi2026_ex15"
    source := ⟨"fusco-sgrizzi-2026", "(15)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni lo pensa a costruire domani."
    discourseSegments := []
    glossedTokens := [("Gianni", "Gianni"), ("lo", "it"), ("pensa", "think-PRS.3SG"), ("a", "to"), ("costruire", "build"), ("domani.", "tomorrow")]
    translation := "Gianni thinks about building it tomorrow."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("size", "aP"), ("diagnostic", "cliticClimbing"), ("grammatical", "no")]
    comment := "Under an attitude verb the a-infinitive does not let the clitic climb."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex16 : LinguisticExample :=
  { id := "fuscosgrizzi2026_ex16"
    source := ⟨"fusco-sgrizzi-2026", "(16)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Gianni mi ha convinto a non salutare più il capo."
    discourseSegments := []
    glossedTokens := [("Gianni", "Gianni"), ("mi", "me.CL"), ("ha", "have-PRS.3SG"), ("convinto", "convince-PST.PTCP"), ("a", "to"), ("non", "not"), ("salutare", "greet-INF"), ("più", "anymore"), ("il", "the"), ("capo.", "boss")]
    translation := "Gianni has convinced me not to say hello to the boss anymore."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("size", "aP"), ("diagnostic", "negation"), ("grammatical", "yes")]
    comment := "The a-infinitive hosts negation, so it projects functional structure above vP."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex17 : LinguisticExample :=
  { id := "fuscosgrizzi2026_ex17"
    source := ⟨"fusco-sgrizzi-2026", "(17)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ieri Gianni mi ha convinto a comprare una macchina nuova il mese prossimo."
    discourseSegments := []
    glossedTokens := [("Ieri", "yesterday"), ("Gianni", "Gianni"), ("mi", "me.CL"), ("ha", "have-PRS.3SG"), ("convinto", "convince-PST.PTCP"), ("a", "to"), ("comprare", "buy-INF"), ("una", "a"), ("macchina", "car"), ("nuova", "new"), ("il", "the"), ("mese", "month"), ("prossimo.", "next")]
    translation := "Yesterday Gianni convinced me to buy a new car next month."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("size", "aP"), ("diagnostic", "independentTime"), ("grammatical", "yes")]
    comment := "The a-infinitive is its own temporal domain and takes a temporal adverb of its own."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex18 : LinguisticExample :=
  { id := "fuscosgrizzi2026_ex18"
    source := ⟨"fusco-sgrizzi-2026", "(18)"⟩
    reportedIn := none
    language := "ital1282"
    primaryText := "Ieri Gianni ha provato a riparare la macchina il mese prossimo."
    discourseSegments := []
    glossedTokens := [("Ieri", "yesterday"), ("Gianni", "Gianni"), ("ha", "have-PRS.3SG"), ("provato", "try-PST.PTCP"), ("a", "to"), ("riparare", "repair"), ("la", "the"), ("macchina", "car"), ("il", "the"), ("mese", "month"), ("prossimo.", "next")]
    translation := "Yesterday Gianni has tried to repair the car next month."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("size", "vP"), ("diagnostic", "independentTime"), ("grammatical", "no")]
    comment := "A restructuring infinitive depends on the matrix clause for its temporal specification."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex4a, ex4b, ex4a_control, ex4b_control, ex11a, ex11b, ex12, ex13, ex14, ex15, ex16, ex17, ex18]

end FuscoSgrizzi2026.Examples
