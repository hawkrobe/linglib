module

public import Linglib.Data.Examples.Schema

/-!
# `SeeligerRepp2018` — typed example data

Auto-generated from `Linglib/Data/Examples/SeeligerRepp2018.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace SeeligerRepp2018.Examples`.
-/

@[expose] public section

namespace SeeligerRepp2018.Examples

open Data.Examples

def en_pdq : LinguisticExample :=
  { id := "seeligerrepp2018_en_pdq"
    source := ⟨"seeliger-repp-2018", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Peter is coming?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Paul and Maria are looking at a list of guests for tonight's dinner party. Maria sees Peter's name on the list."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("type", "PDQ"), ("declarative", "p"), ("evidential", "+positive"), ("epistemic", "-positive")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def de_pdq : LinguisticExample :=
  { id := "seeligerrepp2018_de_pdq"
    source := ⟨"seeliger-repp-2018", "(5b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Peter kommt?"
    discourseSegments := []
    glossedTokens := [("Peter", "Peter"), ("kommt", "comes")]
    translation := "Peter is coming?"
    context := "Paul and Maria are looking at a list of guests for tonight's dinner party. Maria sees Peter's name on the list."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("type", "PDQ"), ("declarative", "p"), ("evidential", "+positive"), ("epistemic", "-positive")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def sv_pdq : LinguisticExample :=
  { id := "seeligerrepp2018_sv_pdq"
    source := ⟨"seeliger-repp-2018", "(5c)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Peter kommer?"
    discourseSegments := []
    glossedTokens := [("Peter", "Peter"), ("kommer", "comes")]
    translation := "Peter is coming?"
    context := "Paul and Maria are looking at a list of guests for tonight's dinner party. Maria sees Peter's name on the list."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("type", "PDQ"), ("declarative", "p"), ("evidential", "+positive"), ("epistemic", "-positive")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def en_ndq : LinguisticExample :=
  { id := "seeligerrepp2018_en_ndq"
    source := ⟨"seeliger-repp-2018", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Peter isn't coming?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Paul and Maria are looking at a list of guests for tonight's dinner party. Maria sees that Peter's name on the list is crossed out."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("type", "NDQ"), ("declarative", "not p"), ("evidential", "+negative"), ("epistemic", "-negative")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def de_ndq : LinguisticExample :=
  { id := "seeligerrepp2018_de_ndq"
    source := ⟨"seeliger-repp-2018", "(6b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Peter kommt nicht?"
    discourseSegments := []
    glossedTokens := [("Peter", "Peter"), ("kommt", "comes"), ("nicht", "not")]
    translation := "Peter isn't coming?"
    context := "Paul and Maria are looking at a list of guests for tonight's dinner party. Maria sees that Peter's name on the list is crossed out."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("type", "NDQ"), ("declarative", "not p"), ("evidential", "+negative"), ("epistemic", "-negative")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def sv_ndq : LinguisticExample :=
  { id := "seeligerrepp2018_sv_ndq"
    source := ⟨"seeliger-repp-2018", "(6c)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Peter kommer inte?"
    discourseSegments := []
    glossedTokens := [("Peter", "Peter"), ("kommer", "comes"), ("inte", "not")]
    translation := "Peter isn't coming?"
    context := "Paul and Maria are looking at a list of guests for tonight's dinner party. Maria sees that Peter's name on the list is crossed out."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2"), ("type", "NDQ"), ("declarative", "not p"), ("evidential", "+negative"), ("epistemic", "-negative")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def en_nrq : LinguisticExample :=
  { id := "seeligerrepp2018_en_nrq"
    source := ⟨"seeliger-repp-2018", "(7a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Surely Peter isn't coming?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Paul and Maria are looking at a list of guests for tonight's dinner party. Maria sees Peter's name on the list."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("type", "NRQ"), ("declarative", "not p"), ("evidential", "+positive"), ("epistemic", "+negative")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def de_nrq_doch_wohl : LinguisticExample :=
  { id := "seeligerrepp2018_de_nrq_doch_wohl"
    source := ⟨"seeliger-repp-2018", "(7b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Peter kommt doch wohl nicht?"
    discourseSegments := []
    glossedTokens := [("Peter", "Peter"), ("kommt", "comes"), ("doch", "mp"), ("wohl", "mp"), ("nicht", "not")]
    translation := "Surely Peter isn't coming?"
    context := "Paul and Maria are looking at a list of guests for tonight's dinner party. Maria sees Peter's name on the list."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("type", "NRQ"), ("declarative", "not p"), ("evidential", "+positive"), ("epistemic", "+negative")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def sv_nrq_fronted_negation : LinguisticExample :=
  { id := "seeligerrepp2018_sv_nrq_fronted_negation"
    source := ⟨"seeliger-repp-2018", "(7c)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Inte kommer Peter?"
    discourseSegments := []
    glossedTokens := [("Inte", "not"), ("kommer", "comes"), ("Peter", "Peter")]
    translation := "Surely Peter isn't coming?"
    context := "Paul and Maria are looking at a list of guests for tonight's dinner party. Maria sees Peter's name on the list."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("type", "NRQ"), ("declarative", "not p"), ("evidential", "+positive"), ("epistemic", "+negative"), ("negation", "fronted"), ("väl", "no"), ("men", "no"), ("visst/nog", "no"), ("evidence", "direct")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def en_prq : LinguisticExample :=
  { id := "seeligerrepp2018_en_prq"
    source := ⟨"seeliger-repp-2018", "(8a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Surely Peter is coming?"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Paul and Maria are looking at a list of guests for tonight's dinner party. Maria sees that Peter's name on the list is crossed out."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("type", "PRQ"), ("declarative", "p"), ("evidential", "+negative"), ("epistemic", "+positive")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def de_prq_doch_wohl : LinguisticExample :=
  { id := "seeligerrepp2018_de_prq_doch_wohl"
    source := ⟨"seeliger-repp-2018", "(8b)"⟩
    reportedIn := none
    language := "stan1295"
    primaryText := "Peter kommt doch wohl?"
    discourseSegments := []
    glossedTokens := [("Peter", "Peter"), ("kommt", "comes"), ("doch", "mp"), ("wohl", "mp")]
    translation := "Surely Peter is coming?"
    context := "Paul and Maria are looking at a list of guests for tonight's dinner party. Maria sees that Peter's name on the list is crossed out."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("type", "PRQ"), ("declarative", "p"), ("evidential", "+negative"), ("epistemic", "+positive")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def sv_prq_men_val : LinguisticExample :=
  { id := "seeligerrepp2018_sv_prq_men_val"
    source := ⟨"seeliger-repp-2018", "(8c)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Men Peter kommer väl?"
    discourseSegments := []
    glossedTokens := [("Men", "but"), ("Peter", "Peter"), ("kommer", "comes"), ("väl", "mp")]
    translation := "Surely Peter is coming?"
    context := "Paul and Maria are looking at a list of guests for tonight's dinner party. Maria sees that Peter's name on the list is crossed out."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "3"), ("type", "PRQ"), ("declarative", "p"), ("evidential", "+negative"), ("epistemic", "+positive"), ("negation", "none"), ("väl", "yes"), ("men", "yes"), ("visst/nog", "no"), ("evidence", "direct")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def sv_prq_visst : LinguisticExample :=
  { id := "seeligerrepp2018_sv_prq_visst"
    source := ⟨"seeliger-repp-2018", "(8c′)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Visst kommer Peter?"
    discourseSegments := []
    glossedTokens := [("Visst", "mp"), ("kommer", "comes"), ("Peter", "Peter")]
    translation := "Surely Peter is coming?"
    context := "Paul and Maria are looking at a list of guests for tonight's dinner party. Maria sees that Peter's name on the list is crossed out."
    judgment := .acceptable
    alternatives := [("Nog kommer Peter?", .acceptable)]
    readings := []
    paperFeatures := [("section", "3"), ("type", "PRQ"), ("declarative", "p"), ("evidential", "+negative"), ("epistemic", "+positive"), ("negation", "none"), ("väl", "no"), ("men", "no"), ("visst/nog", "yes"), ("evidence", "direct")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def sv_23a : LinguisticExample :=
  { id := "seeligerrepp2018_sv_23a"
    source := ⟨"seeliger-repp-2018", "(23a)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Noah är till sjöss?"
    discourseSegments := ["Noah is coming to the party tomorrow.", "Noah är till sjöss?"]
    glossedTokens := [("Noah", "Noah"), ("är", "is"), ("till", "to"), ("sjöss", "sea")]
    translation := "Surely Noah is at sea?"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.3"), ("type", "PRQ"), ("negation", "none"), ("väl", "no"), ("men", "no"), ("visst/nog", "no"), ("evidence", "indirect")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def sv_23b : LinguisticExample :=
  { id := "seeligerrepp2018_sv_23b"
    source := ⟨"seeliger-repp-2018", "(23b)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Men Noah är väl till sjöss?"
    discourseSegments := ["Noah is coming to the party tomorrow.", "Men Noah är väl till sjöss?"]
    glossedTokens := [("Men", "but"), ("Noah", "Noah"), ("är", "is"), ("väl", "mp"), ("till", "to"), ("sjöss", "sea")]
    translation := "Surely Noah is at sea?"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.3"), ("type", "PRQ"), ("negation", "none"), ("väl", "yes"), ("men", "yes"), ("visst/nog", "no"), ("evidence", "indirect")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def sv_23c : LinguisticExample :=
  { id := "seeligerrepp2018_sv_23c"
    source := ⟨"seeliger-repp-2018", "(23c)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Visst är Noah till sjöss?"
    discourseSegments := ["Noah is coming to the party tomorrow.", "Visst är Noah till sjöss?"]
    glossedTokens := [("Visst", "mp"), ("är", "is"), ("Noah", "Noah"), ("till", "to"), ("sjöss", "sea")]
    translation := "Surely Noah is at sea?"
    context := ""
    judgment := .unacceptable
    alternatives := [("Nog är Noah till sjöss?", .unacceptable)]
    readings := []
    paperFeatures := [("section", "5.3"), ("type", "PRQ"), ("negation", "none"), ("väl", "no"), ("men", "no"), ("visst/nog", "yes"), ("evidence", "indirect")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def sv_23d : LinguisticExample :=
  { id := "seeligerrepp2018_sv_23d"
    source := ⟨"seeliger-repp-2018", "(23d)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Visst är väl Noah till sjöss?"
    discourseSegments := ["Noah is coming to the party tomorrow.", "Visst är väl Noah till sjöss?"]
    glossedTokens := [("Visst", "mp"), ("är", "is"), ("väl", "mp"), ("Noah", "Noah"), ("till", "to"), ("sjöss", "sea")]
    translation := "Surely Noah is at sea?"
    context := ""
    judgment := .unacceptable
    alternatives := [("Nog är väl Noah till sjöss?", .unacceptable)]
    readings := []
    paperFeatures := [("section", "5.3"), ("type", "PRQ"), ("negation", "none"), ("väl", "yes"), ("men", "no"), ("visst/nog", "yes"), ("evidence", "indirect")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def sv_24a : LinguisticExample :=
  { id := "seeligerrepp2018_sv_24a"
    source := ⟨"seeliger-repp-2018", "(24a)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Noah är inte till sjöss?"
    discourseSegments := ["Noah is not coming to the party tomorrow.", "Noah är inte till sjöss?"]
    glossedTokens := [("Noah", "Noah"), ("är", "is"), ("inte", "not"), ("till", "to"), ("sjöss", "sea")]
    translation := "Surely Noah is not at sea?"
    context := "Whenever Noah is on shore leave, he always visits every party."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.3"), ("type", "NRQ"), ("negation", "low"), ("väl", "no"), ("men", "no"), ("visst/nog", "no"), ("evidence", "indirect")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def sv_24b : LinguisticExample :=
  { id := "seeligerrepp2018_sv_24b"
    source := ⟨"seeliger-repp-2018", "(24b)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Noah är väl inte till sjöss?"
    discourseSegments := ["Noah is not coming to the party tomorrow.", "Noah är väl inte till sjöss?"]
    glossedTokens := [("Noah", "Noah"), ("är", "is"), ("väl", "mp"), ("inte", "not"), ("till", "to"), ("sjöss", "sea")]
    translation := "Surely Noah is not at sea?"
    context := "Whenever Noah is on shore leave, he always visits every party."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.3"), ("type", "NRQ"), ("negation", "low"), ("väl", "yes"), ("men", "no"), ("visst/nog", "no"), ("evidence", "indirect")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def sv_24c : LinguisticExample :=
  { id := "seeligerrepp2018_sv_24c"
    source := ⟨"seeliger-repp-2018", "(24c)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Inte är Noah till sjöss?"
    discourseSegments := ["Noah is not coming to the party tomorrow.", "Inte är Noah till sjöss?"]
    glossedTokens := [("Inte", "not"), ("är", "is"), ("Noah", "Noah"), ("till", "to"), ("sjöss", "sea")]
    translation := "Surely Noah is not at sea?"
    context := "Whenever Noah is on shore leave, he always visits every party."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.3"), ("type", "NRQ"), ("negation", "fronted"), ("väl", "no"), ("men", "no"), ("visst/nog", "no"), ("evidence", "indirect")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def sv_24d : LinguisticExample :=
  { id := "seeligerrepp2018_sv_24d"
    source := ⟨"seeliger-repp-2018", "(24d)"⟩
    reportedIn := none
    language := "swed1254"
    primaryText := "Inte är väl Noah till sjöss?"
    discourseSegments := ["Noah is not coming to the party tomorrow.", "Inte är väl Noah till sjöss?"]
    glossedTokens := [("Inte", "not"), ("är", "is"), ("väl", "mp"), ("Noah", "Noah"), ("till", "to"), ("sjöss", "sea")]
    translation := "Surely Noah is not at sea?"
    context := "Whenever Noah is on shore leave, he always visits every party."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.3"), ("type", "NRQ"), ("negation", "fronted"), ("väl", "yes"), ("men", "no"), ("visst/nog", "no"), ("evidence", "indirect")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [en_pdq, de_pdq, sv_pdq, en_ndq, de_ndq, sv_ndq, en_nrq, de_nrq_doch_wohl, sv_nrq_fronted_negation, en_prq, de_prq_doch_wohl, sv_prq_men_val, sv_prq_visst, sv_23a, sv_23b, sv_23c, sv_23d, sv_24a, sv_24b, sv_24c, sv_24d]

end SeeligerRepp2018.Examples
