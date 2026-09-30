module

public import Linglib.Data.Examples.Schema

/-!
# `Cacchioli2026` — typed example data

Auto-generated from `Linglib/Data/Examples/Cacchioli2026.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Cacchioli2026.Examples`.
-/

@[expose] public section

namespace Cacchioli2026.Examples

open Data.Examples

def ex_5b : LinguisticExample :=
  { id := "cacchioli2026_5b"
    source := ⟨"cacchioli-2026", "ex. (5b)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "mɨs dɨm-ay ʔaj-ts'awɛti-n"
    glossedTokens := [("mɨs", "with"), ("dɨm-ay", "cat-POSS.1S"), ("ʔaj-Ø-ts'awɛti-n", "NEG-SM.1S-play.IPFV-NEG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "root"), ("neg_suffix", "present")] }

def ex_12a : LinguisticExample :=
  { id := "cacchioli2026_12a"
    source := ⟨"cacchioli-2026", "ex. (12a)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "ʔɨt-om ʔanɛ z-ɛj-nbɨb-om mɛts'ħafti ʔab-t-i ʔarmadyo ʔall-ɛwo"
    glossedTokens := [("ʔɨt-om", "DIST-MP"), ("ʔanɛ", "I"), ("z-ɛj-Ø-nbɨb-om", "REL-NEG-SM.1S-read.IPFV-OM.3MP"), ("mɛts'ħafti", "book.MP"), ("ʔab-t-i", "PREP-DIST-MS"), ("ʔarmadyo", "cabinet"), ("ʔall-ɛwo", "BE1.PRES-SM.3MP")]
    context := ""
    judgment := .acceptable
    alternatives := [("ʔɨt-om ʔanɛ z-ɨ-nbɨb-om-n mɛts'ħafti ʔab-t-i ʔarmadyo ʔall-ɛwo", .ungrammatical), ("ʔɨt-om ʔanɛ z-ɛj-nbɨb-om-n mɛts'ħafti ʔab-t-i ʔarmadyo ʔall-ɛwo", .ungrammatical)]
    readings := []
    paperFeatures := [("clause", "relative"), ("neg_suffix", "absent")] }

def ex_14 : LinguisticExample :=
  { id := "cacchioli2026_14"
    source := ⟨"cacchioli-2026", "ex. (14)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "Kidanɛ mɛts'ħafti z-ɛj-nbib ji-mɛsɨl"
    glossedTokens := [("Kidanɛ", "Kidane"), ("mɛts'ħafti", "book.MP"), ("z-ɛj-Ø-nbib", "REL-NEG-SM.3MS-read.IPFV"), ("ji-mɛsɨl", "SM.3MS-seem.IPFV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "seem"), ("neg_suffix", "absent")] }

def ex_15 : LinguisticExample :=
  { id := "cacchioli2026_15"
    source := ⟨"cacchioli-2026", "ex. (15)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "nɨssu ʔɨntɛ z-ɛj-xɛjɨd k-ɨ-bɛli ʔijj-ɛ"
    glossedTokens := [("nɨssu", "he"), ("ʔɨntɛ", "if"), ("z-ɛj-Ø-xɛjɨd", "REL-NEG-SM.3MS-leave.IPFV"), ("k-ɨ-bɛli", "SBJ-SM.1S-cry.IPFV"), ("ʔijj-ɛ", "BE2.PRES-SM.1S")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "conditional"), ("neg_suffix", "absent")] }

def ex_16 : LinguisticExample :=
  { id := "cacchioli2026_16"
    source := ⟨"cacchioli-2026", "ex. (16)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "ʔaman ʔɨntay kɛm-z-ɛj-fɛttu ħatit-u-ni"
    glossedTokens := [("ʔaman", "Aman"), ("ʔɨntay", "what"), ("kɛm-z-ɛj-Ø-fɛttu", "COMP-REL-NEG-SM.1S-like.IPFV"), ("ħatit-u-ni", "ask.GER-SM.3MS-OM.1S")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "complement"), ("neg_suffix", "absent"), ("verb_class", "utterance"), ("typer", "kemzi"), ("matrix_verb", "ask")] }

def ex_20 : LinguisticExample :=
  { id := "cacchioli2026_20"
    source := ⟨"cacchioli-2026", "ex. (20)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "k-ɛj-bɛki fɛttin-ɛ"
    glossedTokens := [("k-ɛj-Ø-bɛki", "SBJ-NEG-SM.1S-cry.IPFV"), ("fɛttin-ɛ", "try.GER-SM.1S")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "subjunctive"), ("neg_suffix", "absent"), ("verb_class", "control"), ("typer", "ki"), ("matrix_verb", "try")] }

def ex_21 : LinguisticExample :=
  { id := "cacchioli2026_21"
    source := ⟨"cacchioli-2026", "ex. (21)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "dɛrho k-ɛj-nɛfɨr ʔaziz-u"
    glossedTokens := [("dɛrho", "chicken"), ("k-ɛj-Ø-nɛfɨr", "SBJ-NEG-SM.3MS-fly.IPFV"), ("ʔaziz-u", "order.GER-SM.3MS")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "subjunctive"), ("neg_suffix", "absent"), ("verb_class", "directive"), ("typer", "ki"), ("matrix_verb", "order")] }

def ex_22 : LinguisticExample :=
  { id := "cacchioli2026_22"
    source := ⟨"cacchioli-2026", "ex. (22)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "ʔɨt-a sɛbɛjti k-ɛj-tɨ-xɛjjɨd dɛli-na"
    glossedTokens := [("ʔɨt-a", "DIST-FS"), ("sɛbɛjti", "woman"), ("k-ɛj-tɨ-xɛjjɨd", "SBJ-NEG-SM.3FS-go.IPFV"), ("dɛli-na", "want.GER-SM.1P")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "subjunctive"), ("neg_suffix", "absent"), ("verb_class", "desire"), ("typer", "ki"), ("matrix_verb", "want")] }

def ex_23 : LinguisticExample :=
  { id := "cacchioli2026_23"
    source := ⟨"cacchioli-2026", "ex. (23)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "n-ɨt-i ʔanbɛsa k-ɛj-bɛrbɛr qɛs tɛzawir-ɛ"
    glossedTokens := [("n-ɨt-i", "DOM-DIST-MS"), ("ʔanbɛsa", "lion"), ("k-ɛj-Ø-bɛrbɛr", "SBJ-NEG-SM.3MS-wake up.IPFV"), ("qɛs", "slowly"), ("tɛzawir-ɛ", "walk.GER-SM.1S")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "purpose"), ("neg_suffix", "absent")] }

def ex_24 : LinguisticExample :=
  { id := "cacchioli2026_24"
    source := ⟨"cacchioli-2026", "ex. (24)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "Tɛwɛldɛ ʔɨħmɨlti ʔaj-k-ɨ-bɛlʔɨ-n ʔijj-u"
    glossedTokens := [("Tɛwɛldɛ", "Tewelde"), ("ʔɨħmɨlti", "vegetables"), ("ʔaj-k-ɨ-bɛlʔɨ-n", "NEG-SBJ-SM.3MS-eat.IPFV-NEG"), ("ʔijj-u", "BE2.PRES-SM.3MS")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clause", "future"), ("neg_suffix", "present")] }

def ex_25 : LinguisticExample :=
  { id := "cacchioli2026_25"
    source := ⟨"cacchioli-2026", "ex. (25)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "dɛrho ʔaj-nɨfɨri-n ʔɨl-ɛ gɛlits'-ɛ"
    glossedTokens := [("dɛrho", "chicken"), ("ʔaj-Ø-nɨfɨri-n", "NEG-SM.3MS-fly.IPFV-NEG"), ("ʔɨl-ɛ", "COMP-SM.1S"), ("gɛlits'-ɛ", "explain.GER-SM.1S")]
    context := ""
    judgment := .acceptable
    alternatives := [("dɛrho ʔaj-nɨfɨri ʔɨl-ɛ gɛlits'-ɛ", .ungrammatical)]
    readings := []
    paperFeatures := [("clause", "ilu"), ("neg_suffix", "present"), ("verb_class", "utterance"), ("typer", "ilu"), ("matrix_verb", "explain")] }

def ex_29 : LinguisticExample :=
  { id := "cacchioli2026_29"
    source := ⟨"cacchioli-2026", "ex. (29)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "bzuħ gɨziɛ nɨsu sinɛma kɛm-z-ɨ-xɛjjɨd ji-fɛllɨt'"
    glossedTokens := [("bzuħ gɨziɛ", "often"), ("nɨsu", "he"), ("sinɛma", "cinema"), ("kɛm-z-ɨ-xɛjjɨd", "COMP-REL-SM.3MS-go.IPFV"), ("ji-fɛllɨt'", "SM.1S-know.IPFV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb_class", "factive"), ("typer", "kemzi"), ("matrix_verb", "know")] }

def ex_30 : LinguisticExample :=
  { id := "cacchioli2026_30"
    source := ⟨"cacchioli-2026", "ex. (30)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "fadus gɨziɛ kɛm-z-ɨ-mɛts'ɨʔ rɛsiʕ-ɛ"
    glossedTokens := [("fadus", "noon"), ("gɨziɛ", "time"), ("kɛm-z-ɨ-mɛts'ɨʔ", "COMP-REL-SM.3MS-come.IPFV"), ("rɛsiʕ-ɛ", "forget.GER-SM.1S")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb_class", "factive"), ("typer", "kemzi"), ("matrix_verb", "forget")] }

def ex_31 : LinguisticExample :=
  { id := "cacchioli2026_31"
    source := ⟨"cacchioli-2026", "ex. (31)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "kɛm-z-ɨ-fɛt-wa ji-ʔɛmɨn"
    glossedTokens := [("kɛm-z-ɨ-fɛt-wa", "COMP-REL-SM.3MS-like.IPFV-OM.3FS"), ("ji-ʔɛmɨn", "SM.3MS-admit.IPFV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb_class", "factive"), ("typer", "kemzi"), ("matrix_verb", "admit")] }

def ex_32 : LinguisticExample :=
  { id := "cacchioli2026_32"
    source := ⟨"cacchioli-2026", "ex. (32)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "ħaʃɛrɛ-tat kɛm-z-ɨ-fɛttu ji-qɛbɨl"
    glossedTokens := [("ħaʃɛrɛ-tat", "spider-P"), ("kɛm-z-ɨ-fɛttu", "COMP-REL-SM.1S-like.IPFV"), ("ji-qɛbɨl", "SM.1S-accept.IPFV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb_class", "factive"), ("typer", "kemzi"), ("matrix_verb", "accept")] }

def ex_33 : LinguisticExample :=
  { id := "cacchioli2026_33"
    source := ⟨"cacchioli-2026", "ex. (33)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "ʔaman Tɛsfay mɛts'ħafti kɛm-z-ɨ-ʃɛjɨt ji-ħasɨb"
    glossedTokens := [("ʔaman", "Aman"), ("Tɛsfay", "Tesfay"), ("mɛts'ħafti", "book.FP"), ("kɛm-z-ɨ-ʃɛjɨt", "COMP-REL-SM.3MS-sell.IPFV"), ("ji-ħasɨb", "SM.3MS-think.IPFV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb_class", "cognitive_non_factive"), ("typer", "kemzi"), ("matrix_verb", "think")] }

def ex_34 : LinguisticExample :=
  { id := "cacchioli2026_34"
    source := ⟨"cacchioli-2026", "ex. (34)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "ʔaman Tɛsfay mɛts'ħafti kɛm-z-ɨ-ʃɛjɨt ji-ʔamɨn"
    glossedTokens := [("ʔaman", "Aman"), ("Tɛsfay", "Tesfay"), ("mɛts'ħafti", "book.FP"), ("kɛm-z-ɨ-ʃɛjɨt", "COMP-REL-SM.3MS-sell.IPFV"), ("ji-ʔamɨn", "SM.3MS-believe.IPFV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb_class", "cognitive_non_factive"), ("typer", "kemzi"), ("matrix_verb", "believe")] }

def ex_35 : LinguisticExample :=
  { id := "cacchioli2026_35"
    source := ⟨"cacchioli-2026", "ex. (35)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "nsu gɛnzɛb kɛm-z-ɨ-sɛrrix ji-t'irɨt'r-o"
    glossedTokens := [("nsu", "he"), ("gɛnzɛb", "money"), ("kɛm-z-ɨ-sɛrrix", "COMP-REL-SM.3MS-steal.IPFV"), ("ji-t'irɨt'r-o", "SM.3MS-suspect.IPFV-OM.3MS")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb_class", "cognitive_non_factive"), ("typer", "kemzi"), ("matrix_verb", "suspect")] }

def ex_51 : LinguisticExample :=
  { id := "cacchioli2026_51"
    source := ⟨"cacchioli-2026", "ex. (51)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "qɛbaʔi kɛm-zɨ-kon-ɨt sɛmiʕ-ɛ"
    glossedTokens := [("qɛbaʔi", "painter"), ("kɛm-zɨ-kon-ɨt", "COMP-REL-become.PFV-SM.3FS"), ("sɛmiʕ-ɛ", "hear.GER-SM.1S")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb_class", "perception"), ("typer", "kemzi"), ("matrix_verb", "hear")] }

def ex_52a : LinguisticExample :=
  { id := "cacchioli2026_52a"
    source := ⟨"cacchioli-2026", "ex. (52a)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "nɨsatom kɛm-zɨ-tɛmɛrʕa-wu riʔɛy-ɛ"
    glossedTokens := [("nɨsatom", "they"), ("kɛm-zɨ-Ø-tɛmɛrʕa-wu", "COMP-REL-SM.3MP-marry.IPFV-SM.3MP"), ("riʔɛy-ɛ", "see.GER-SM.1S")]
    context := ""
    judgment := .acceptable
    alternatives := [("nɨsatom kɛm-zɨ-tɛmɛrʕa-wu ʔɨl-ɛ riʔɛy-ɛ", .ungrammatical)]
    readings := []
    paperFeatures := [("verb_class", "perception"), ("typer", "kemzi"), ("matrix_verb", "see")] }

def ex_53 : LinguisticExample :=
  { id := "cacchioli2026_53"
    source := ⟨"cacchioli-2026", "ex. (53)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "nsu gɛnzɛb ji-sɛrrix ʔɨl-ɛ ji-t'irɨt'r-o"
    glossedTokens := [("nsu", "he"), ("gɛnzɛb", "money"), ("ji-sɛrrix", "SM.3MS-steal.IPFV"), ("ʔɨl-ɛ", "COMP-SM.1S"), ("ji-t'irɨt'r-o", "SM.1S-suspect.IPFV-OM.3MS")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb_class", "cognitive_non_factive"), ("typer", "ilu"), ("matrix_verb", "suspect")] }

def ex_54 : LinguisticExample :=
  { id := "cacchioli2026_54"
    source := ⟨"cacchioli-2026", "ex. (54)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "Tɛsfay ʔaman kɛlbi gɛziʔ-u ʔɨl-u ħalim-u"
    glossedTokens := [("Tɛsfay", "Tesfay"), ("ʔaman", "Aman"), ("kɛlbi", "dog"), ("gɛziʔ-u", "buy.GER-SM.3MS"), ("ʔɨl-u", "COMP-SM.3MS"), ("ħalim-u", "dream.GER-SM.3MS")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb_class", "fiction"), ("typer", "ilu"), ("matrix_verb", "dream")] }

def ex_55 : LinguisticExample :=
  { id := "cacchioli2026_55"
    source := ⟨"cacchioli-2026", "ex. (55)"⟩
    reportedIn := none
    language := "tigr1271"
    primaryText := "dɛmamu ʔanats'u ji-bɛlɨʕ-u ʔɨl-ɛ ʔanbib-ɛ"
    glossedTokens := [("dɛmamu", "cat.MP"), ("ʔanats'u", "mouse.MP"), ("ji-bɛlɨʕ-u", "SM.3MP-eat.IPFV-SM.3MP"), ("ʔɨl-ɛ", "COMP-SM.1S"), ("ʔanbib-ɛ", "read.GER-SM.1S")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("verb_class", "utterance"), ("typer", "ilu"), ("matrix_verb", "read")] }

def all : List LinguisticExample := [ex_5b, ex_12a, ex_14, ex_15, ex_16, ex_20, ex_21, ex_22, ex_23, ex_24, ex_25, ex_29, ex_30, ex_31, ex_32, ex_33, ex_34, ex_35, ex_51, ex_52a, ex_53, ex_54, ex_55]

end Cacchioli2026.Examples
