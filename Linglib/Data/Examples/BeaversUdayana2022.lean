import Linglib.Data.Examples.Schema

/-!
# `BeaversUdayana2022` — typed example data

Auto-generated from `Linglib/Data/Examples/BeaversUdayana2022.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BeaversUdayana2022.Examples`.
-/

namespace BeaversUdayana2022.Examples

open Data.Examples

def bu2022_2a : LinguisticExample :=
  { id := "bu2022_2a"
    source := ⟨"beavers-udayana-2022", "(2a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Ali ber-dandan."
    discourseSegments := []
    glossedTokens := [("Ali", "Ali"), ("ber-dandan", "MV-dress")]
    translation := "Ali dressed."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("middle type", "inherent reflexive"), ("root class", "naturally reflexive")]
    comment := "Body-care roots default to the coreferent reading of the suppressed variable."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bu2022_2b : LinguisticExample :=
  { id := "bu2022_2b"
    source := ⟨"beavers-udayana-2022", "(2b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Mobil itu ber-jual dengan mudah."
    discourseSegments := []
    glossedTokens := [("Mobil", "car"), ("itu", "that"), ("ber-jual", "MV-sell"), ("dengan", "with"), ("mudah", "easy")]
    translation := "The car sells easily."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("middle type", "dispositional"), ("reading", "generic")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bu2022_7 : LinguisticExample :=
  { id := "bu2022_7"
    source := ⟨"beavers-udayana-2022", "(7)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Mobil itu ber-jual kemarin."
    discourseSegments := []
    glossedTokens := [("Mobil", "car"), ("itu", "that"), ("ber-jual", "MV-sell"), ("kemarin", "yesterday")]
    translation := "The car sold yesterday."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("middle type", "passive middle"), ("reading", "episodic")]
    comment := "Episodic reading, unlike English dispositionals."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bu2022_9a : LinguisticExample :=
  { id := "bu2022_9a"
    source := ⟨"beavers-udayana-2022", "(9a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Mobil itu ber-jual tapi tidak ada orang yang men-jual=nya."
    discourseSegments := []
    glossedTokens := [("Mobil", "car"), ("itu", "that"), ("ber-jual", "MV-sell"), ("tapi", "but"), ("tidak", "NEG"), ("ada", "exist"), ("orang", "man"), ("yang", "REL"), ("men-jual=nya", "AV-sell=3SG")]
    translation := "The car sells/sold, but nobody sold it."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("middle type", "dispositional"), ("diagnostic", "agent denial")]
    comment := "The unexpressed agent is entailed to exist, as with di- passives."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bu2022_10c : LinguisticExample :=
  { id := "bu2022_10c"
    source := ⟨"beavers-udayana-2022", "(10c)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Mobil itu ber-jual dengan sendiri=nya."
    discourseSegments := []
    glossedTokens := [("Mobil", "car"), ("itu", "that"), ("ber-jual", "MV-sell"), ("dengan", "with"), ("sendiri=nya", "alone=DEF")]
    translation := "The car sold/sells by itself."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("middle type", "dispositional"), ("diagnostic", "dengan sendiri=nya")]
    comment := "'By itself' contradicts the entailed separate causer."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bu2022_11 : LinguisticExample :=
  { id := "bu2022_11"
    source := ⟨"beavers-udayana-2022", "(11)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Mobil itu di-jual oleh Tono."
    discourseSegments := []
    glossedTokens := [("Mobil", "car"), ("itu", "that"), ("di-jual", "PASS-sell"), ("oleh", "by"), ("Tono", "Tono")]
    translation := "The car was sold by Tono."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("voice", "di- passive"), ("diagnostic", "oleh phrase")]
    comment := "The ber- variant *ber-jual oleh Tono is ungrammatical: middles reject oleh."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bu2022_13 : LinguisticExample :=
  { id := "bu2022_13"
    source := ⟨"beavers-udayana-2022", "(13)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Orang itu ber-jual untuk meng-(k)umpul-kan dana."
    discourseSegments := []
    glossedTokens := [("Orang", "man"), ("itu", "that"), ("ber-jual", "MV-sell"), ("untuk", "for"), ("meng-(k)umpul-kan", "AV-collect-CAUS"), ("dana", "fund")]
    translation := "The man sells/sold to collect funds."
    context := "A charity bachelor auction."
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("middle type", "dispositional"), ("diagnostic", "rationale clause")]
    comment := "The suppressed agent cannot control rationale PRO, unlike di- passives (12b)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bu2022_17b : LinguisticExample :=
  { id := "bu2022_17b"
    source := ⟨"beavers-udayana-2022", "(17b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Orang itu ber-dandan dengan sendiri=nya."
    discourseSegments := []
    glossedTokens := [("Orang", "man"), ("itu", "that"), ("ber-dandan", "MV-dress"), ("dengan", "with"), ("sendiri=nya", "alone=DEF")]
    translation := "The man dressed by himself."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("middle type", "inherent reflexive"), ("diagnostic", "dengan sendiri=nya")]
    comment := "The surface subject is the causer, so 'by itself' is licensed."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bu2022_18a : LinguisticExample :=
  { id := "bu2022_18a"
    source := ⟨"beavers-udayana-2022", "(18a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Orang itu ber-cuci=mata."
    discourseSegments := []
    glossedTokens := [("Orang", "man"), ("itu", "that"), ("ber-cuci=mata", "MV-wash=eye")]
    translation := "The man washed his eyes."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("compositional: washed his eyes", .acceptable), ("idiomatic: watched the girls go by (24b)", .acceptable)]
    paperFeatures := [("middle type", "incorporation"), ("object", "incorporated NP")]
    comment := "The agent surfaces as subject; the patient is an incorporated NP."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bu2022_19b : LinguisticExample :=
  { id := "bu2022_19b"
    source := ⟨"beavers-udayana-2022", "(19b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Gadis itu ber-cuci dengan cepat kaki."
    discourseSegments := []
    glossedTokens := [("Gadis", "girl"), ("itu", "that"), ("ber-cuci", "MV-wash"), ("dengan", "with"), ("cepat", "quick"), ("kaki", "leg")]
    translation := "The girl washed her leg quickly."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("middle type", "incorporation"), ("diagnostic", "non-separability")]
    comment := "The incorporated NP cannot be separated from the verb, unlike a meN- object (19a)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bu2022_22 : LinguisticExample :=
  { id := "bu2022_22"
    source := ⟨"beavers-udayana-2022", "(22)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia ber-jual=mobil. Mobil itu mahal."
    discourseSegments := []
    glossedTokens := [("Dia", "3SG"), ("ber-jual=mobil", "MV-sell=car"), ("Mobil", "car"), ("itu", "that"), ("mahal", "expensive")]
    translation := "(S)he sold a car. That car was expensive."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("middle type", "incorporation"), ("diagnostic", "discourse opacity")]
    comment := "The incorporated noun cannot antecede 'that car' — no discourse referent."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bu2022_26b : LinguisticExample :=
  { id := "bu2022_26b"
    source := ⟨"beavers-udayana-2022", "(26b)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Orang itu ber-jual=diri."
    discourseSegments := []
    glossedTokens := [("Orang", "man"), ("itu", "that"), ("ber-jual=diri", "MV-sell=REFL")]
    translation := "The man sold himself."
    context := "E.g. sold into servitude."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("middle type", "incorporated reflexive"), ("object", "diri")]
    comment := "Incorporated diri triggers the coreferent reading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bu2022_28 : LinguisticExample :=
  { id := "bu2022_28"
    source := ⟨"beavers-udayana-2022", "(28)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Orang itu ber-jual=baju=diri."
    discourseSegments := []
    glossedTokens := [("Orang", "man"), ("itu", "that"), ("ber-jual=baju=diri", "MV-sell=dress=REFL")]
    translation := "The man sold the dress."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("middle type", "incorporation"), ("diagnostic", "complementary distribution")]
    comment := "Incorporated diri and an incorporated lexical NP compete for one slot."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bu2022_44a : LinguisticExample :=
  { id := "bu2022_44a"
    source := ⟨"beavers-udayana-2022", "(44a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Tono dan Ali ber-dandan."
    discourseSegments := []
    glossedTokens := [("Tono", "Tono"), ("dan", "and"), ("Ali", "Ali"), ("ber-dandan", "MV-dress")]
    translation := "Tono and Ali dressed/got dressed."
    context := "Tono dressed himself and Ali was dressed by his mother."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("diagnostic", "mixed readings"), ("analysis", "open variable vs existential")]
    comment := "No mixed reflexive/disjoint reading under conjunction — unlike Greek, favoring the open-variable analysis (43)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bu2022_59 : LinguisticExample :=
  { id := "bu2022_59"
    source := ⟨"beavers-udayana-2022", "(59)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Tono ber-topi."
    discourseSegments := []
    glossedTokens := [("Tono", "Tono"), ("ber-topi", "MV-hat")]
    translation := "Tono has a hat on."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("middle type", "conflation"), ("root class", "relational noun")]
    comment := "Relational nouns (body parts, kin, clothing) conflate: the possessor surfaces as subject."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bu2022_62 : LinguisticExample :=
  { id := "bu2022_62"
    source := ⟨"beavers-udayana-2022", "(62)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Dia ber-tangan tapi tidak ada yang men-(t)angan-kan=nya."
    discourseSegments := []
    glossedTokens := [("Dia", "3SG"), ("ber-tangan", "MV-hand"), ("tapi", "but"), ("tidak", "NEG"), ("ada", "exist"), ("yang", "REL"), ("men-(t)angan-kan=nya", "AV-hand-CAUS=3SG")]
    translation := "(S)he has hands but nobody gave him/her hands."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("middle type", "conflation"), ("diagnostic", "change denial")]
    comment := "Conflation middles are purely possessional statives, not change-of-state."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bu2022_67a : LinguisticExample :=
  { id := "bu2022_67a"
    source := ⟨"beavers-udayana-2022", "(67a)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Pasukan itu ter-pecah dua tapi tidak ada yang mem-(p)ecah=nya."
    discourseSegments := []
    glossedTokens := [("Pasukan", "troop"), ("itu", "that"), ("ter-pecah", "MV-break"), ("dua", "two"), ("tapi", "but"), ("tidak", "NEG"), ("ada", "exist"), ("yang", "REL"), ("mem-(p)ecah=nya", "AV-break=3SG")]
    translation := "The troop broke into two but nobody/nothing broke them."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("middle type", "anticausative"), ("diagnostic", "causer denial")]
    comment := "ter- anticausatives lack the entailed external causer of dispositional ber- middles; contrast (74)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def bu2022_74 : LinguisticExample :=
  { id := "bu2022_74"
    source := ⟨"beavers-udayana-2022", "(74)"⟩
    reportedIn := none
    language := "indo1316"
    primaryText := "Pasukan itu ber-pecah dua tapi tidak ada yang mem-(p)ecah=nya."
    discourseSegments := []
    glossedTokens := [("Pasukan", "troop"), ("itu", "that"), ("ber-pecah", "MV-break"), ("dua", "two"), ("tapi", "but"), ("tidak", "NEG"), ("ada", "exist"), ("yang", "REL"), ("mem-(p)ecah=nya", "AV-break=3SG")]
    translation := "The troop broke into two but nobody broke them."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("middle type", "dispositional"), ("diagnostic", "causer denial")]
    comment := "ber- on the same root has only the disjoint (dispositional/passive) reading, so causer denial contradicts."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [bu2022_2a, bu2022_2b, bu2022_7, bu2022_9a, bu2022_10c, bu2022_11, bu2022_13, bu2022_17b, bu2022_18a, bu2022_19b, bu2022_22, bu2022_26b, bu2022_28, bu2022_44a, bu2022_59, bu2022_62, bu2022_67a, bu2022_74]

end BeaversUdayana2022.Examples
