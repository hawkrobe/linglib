module

public import Linglib.Data.Examples.Schema

/-!
# `Dixon1994` — typed example data

Auto-generated from `Linglib/Data/Examples/Dixon1994.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Dixon1994.Examples`.
-/

@[expose] public section

namespace Dixon1994.Examples

open Data.Examples

def ex_1_2_5 : LinguisticExample :=
  { id := "dixon1994_1_2_5"
    source := ⟨"dixon-1994", "§1.2 (5)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma banaga-nyu"
    glossedTokens := [("ŋuma", "father.ABS"), ("banaga-nyu", "return-NONFUT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "simple"), ("function", "S")] }

def ex_1_2_7 : LinguisticExample :=
  { id := "dixon1994_1_2_7"
    source := ⟨"dixon-1994", "§1.2 (7)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma yabu-ŋgu bura-n"
    glossedTokens := [("ŋuma", "father.ABS"), ("yabu-ŋgu", "mother-ERG"), ("bura-n", "see-NONFUT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "simple"), ("function", "AO")] }

def ex_1_2_12 : LinguisticExample :=
  { id := "dixon1994_1_2_12"
    source := ⟨"dixon-1994", "§1.2 (12)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma bural-ŋa-nyu yabu-gu"
    glossedTokens := [("ŋuma", "father.ABS"), ("bural-ŋa-nyu", "see-ANTIPASS-NONFUT"), ("yabu-gu", "mother-DAT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "antipassive"), ("function", "S")] }

def ex_15 : LinguisticExample :=
  { id := "dixon1994_15"
    source := ⟨"dixon-1994", "§6.2.2 (15)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "nyurra ŋana-na bura-n"
    glossedTokens := [("nyurra", "you.all.NOM"), ("ŋana-na", "we.all-ACC"), ("bura-n", "see-NONFUT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "simple"), ("function", "AO")] }

def ex_17 : LinguisticExample :=
  { id := "dixon1994_17"
    source := ⟨"dixon-1994", "§6.2.2 (17)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma banaga-nyu miyanda-nyu"
    glossedTokens := [("ŋuma", "father.ABS"), ("banaga-nyu", "return-NONFUT"), ("miyanda-nyu", "laugh-NONFUT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "S"), ("second", "S"), ("derivation", "none")] }

def ex_19 : LinguisticExample :=
  { id := "dixon1994_19"
    source := ⟨"dixon-1994", "§6.2.2 (19)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma banaga-nyu yabu-ŋgu bura-n"
    glossedTokens := [("ŋuma", "father.ABS"), ("banaga-nyu", "return-NONFUT"), ("yabu-ŋgu", "mother-ERG"), ("bura-n", "see-NONFUT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "S"), ("second", "O"), ("derivation", "none")] }

def ex_20 : LinguisticExample :=
  { id := "dixon1994_20"
    source := ⟨"dixon-1994", "§6.2.2 (20)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋana banaga-nyu nyurra bura-n"
    glossedTokens := [("ŋana", "we.all.NOM"), ("banaga-nyu", "return-NONFUT"), ("nyurra", "you.all.NOM"), ("bura-n", "see-NONFUT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "S"), ("second", "O"), ("derivation", "none")] }

def ex_21 : LinguisticExample :=
  { id := "dixon1994_21"
    source := ⟨"dixon-1994", "§6.2.2 (21)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma yabu-ŋgu bura-n banaga-nyu"
    glossedTokens := [("ŋuma", "father.ABS"), ("yabu-ŋgu", "mother-ERG"), ("bura-n", "see-NONFUT"), ("banaga-nyu", "return-NONFUT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "O"), ("second", "S"), ("derivation", "none")] }

def ex_24 : LinguisticExample :=
  { id := "dixon1994_24"
    source := ⟨"dixon-1994", "§6.2.2 (24)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma yabu-ŋgu bura-n jaja-ŋgu ŋamba-n"
    glossedTokens := [("ŋuma", "father.ABS"), ("yabu-ŋgu", "mother-ERG"), ("bura-n", "see-NONFUT"), ("jaja-ŋgu", "child-ERG"), ("ŋamba-n", "hear-NONFUT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "O"), ("second", "O"), ("derivation", "none")] }

def ex_28 : LinguisticExample :=
  { id := "dixon1994_28"
    source := ⟨"dixon-1994", "§6.2.2 (28)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma yabu-ŋgu bura-n (yabu-ŋgu) ŋamba-n"
    glossedTokens := [("ŋuma", "father.ABS"), ("yabu-ŋgu", "mother-ERG"), ("bura-n", "see-NONFUT"), ("(yabu-ŋgu)", "mother-ERG"), ("ŋamba-n", "hear-NONFUT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "O"), ("second", "O"), ("derivation", "none")] }

def ex_32 : LinguisticExample :=
  { id := "dixon1994_32"
    source := ⟨"dixon-1994", "§6.2.2 (32)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma bural-ŋa-nyu yabu-gu"
    glossedTokens := [("ŋuma", "father.ABS"), ("bural-ŋa-nyu", "see-ANTIPASS-NONFUT"), ("yabu-gu", "mother-DAT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "antipassive"), ("function", "S")] }

def ex_33 : LinguisticExample :=
  { id := "dixon1994_33"
    source := ⟨"dixon-1994", "§6.2.2 (33)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋana bural-ŋa-nyu nyurra-ŋgu"
    glossedTokens := [("ŋana", "we.all.NOM"), ("bural-ŋa-nyu", "see-ANTIPASS-NONFUT"), ("nyurra-ŋgu", "you.all-DAT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "antipassive"), ("function", "S")] }

def ex_34 : LinguisticExample :=
  { id := "dixon1994_34"
    source := ⟨"dixon-1994", "§6.2.2 (34)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma banaga-nyu bural-ŋa-nyu yabu-gu"
    glossedTokens := [("ŋuma", "father.ABS"), ("banaga-nyu", "return-NONFUT"), ("bural-ŋa-nyu", "see-ANTIPASS-NONFUT"), ("yabu-gu", "mother-DAT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "S"), ("second", "A"), ("derivation", "antipassive")] }

def ex_36 : LinguisticExample :=
  { id := "dixon1994_36"
    source := ⟨"dixon-1994", "§6.2.2 (36)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma jaja-ŋgu ŋamba-n bural-ŋa-nyu yabu-gu"
    glossedTokens := [("ŋuma", "father.ABS"), ("jaja-ŋgu", "child-ERG"), ("ŋamba-n", "hear-NONFUT"), ("bural-ŋa-nyu", "see-ANTIPASS-NONFUT"), ("yabu-gu", "mother-DAT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "O"), ("second", "A"), ("derivation", "antipassive")] }

def ex_39 : LinguisticExample :=
  { id := "dixon1994_39"
    source := ⟨"dixon-1994", "§6.2.2 (39)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma yabu-ŋgu ŋamba-n bural-ŋa-nyu yabu-gu"
    glossedTokens := [("ŋuma", "father.ABS"), ("yabu-ŋgu", "mother-ERG"), ("ŋamba-n", "hear-NONFUT"), ("bural-ŋa-nyu", "see-ANTIPASS-NONFUT"), ("yabu-gu", "mother-DAT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "O"), ("second", "A"), ("derivation", "antipassive")] }

def ex_42 : LinguisticExample :=
  { id := "dixon1994_42"
    source := ⟨"dixon-1994", "§6.2.2 (42)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma bural-ŋa-nyu yabu-gu banaga-nyu"
    glossedTokens := [("ŋuma", "father.ABS"), ("bural-ŋa-nyu", "see-ANTIPASS-NONFUT"), ("yabu-gu", "mother-DAT"), ("banaga-nyu", "return-NONFUT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "A"), ("second", "S"), ("derivation", "antipassive")] }

def ex_44 : LinguisticExample :=
  { id := "dixon1994_44"
    source := ⟨"dixon-1994", "§6.2.2 (44)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma bural-ŋa-nyu yabu-gu jaja-ŋgu ŋamba-n"
    glossedTokens := [("ŋuma", "father.ABS"), ("bural-ŋa-nyu", "see-ANTIPASS-NONFUT"), ("yabu-gu", "mother-DAT"), ("jaja-ŋgu", "child-ERG"), ("ŋamba-n", "hear-NONFUT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "A"), ("second", "O"), ("derivation", "antipassive")] }

def ex_46 : LinguisticExample :=
  { id := "dixon1994_46"
    source := ⟨"dixon-1994", "§6.2.2 (46)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "yabu ŋuma-ŋgu bura-n (ŋuma) banaga-ŋurra"
    glossedTokens := [("yabu", "mother.ABS"), ("ŋuma-ŋgu", "father-ERG"), ("bura-n", "see-NONFUT"), ("(ŋuma)", "father.ABS"), ("banaga-ŋurra", "return-ŊURRA")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "A"), ("second", "S"), ("derivation", "ngurra")] }

def ex_52 : LinguisticExample :=
  { id := "dixon1994_52"
    source := ⟨"dixon-1994", "§6.2.2 (52)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma bural-ŋa-nyu yabu-gu ŋambal-ŋa-nyu jaja-gu"
    glossedTokens := [("ŋuma", "father.ABS"), ("bural-ŋa-nyu", "see-ANTIPASS-NONFUT"), ("yabu-gu", "mother-DAT"), ("ŋambal-ŋa-nyu", "hear-ANTIPASS-NONFUT"), ("jaja-gu", "child-DAT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "A"), ("second", "A"), ("derivation", "antipassive")] }

def ex_56 : LinguisticExample :=
  { id := "dixon1994_56"
    source := ⟨"dixon-1994", "§6.2.2 (56)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma banaga-nyu yabu-ŋgu bura-li"
    glossedTokens := [("ŋuma", "father.ABS"), ("banaga-nyu", "return-NONFUT"), ("yabu-ŋgu", "mother-ERG"), ("bura-li", "see-PURP")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "purposive"), ("first", "S"), ("second", "O"), ("derivation", "none")] }

def ex_57 : LinguisticExample :=
  { id := "dixon1994_57"
    source := ⟨"dixon-1994", "§6.2.2 (57)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma banaga-nyu bural-ŋa-ygu yabu-gu"
    glossedTokens := [("ŋuma", "father.ABS"), ("banaga-nyu", "return-NONFUT"), ("bural-ŋa-ygu", "see-ANTIPASS-PURP"), ("yabu-gu", "mother-DAT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "purposive"), ("first", "S"), ("second", "A"), ("derivation", "antipassive")] }

def ex_59 : LinguisticExample :=
  { id := "dixon1994_59"
    source := ⟨"dixon-1994", "§6.2.2 (59)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "yabu ŋuma-ŋgu giga-n gubi-ŋgu mawa-li"
    glossedTokens := [("yabu", "mother.ABS"), ("ŋuma-ŋgu", "father-ERG"), ("giga-n", "tell.to.do-NONFUT"), ("gubi-ŋgu", "doctor-ERG"), ("mawa-li", "examine-PURP")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "purposive"), ("first", "O"), ("second", "O"), ("derivation", "none")] }

def ex_60 : LinguisticExample :=
  { id := "dixon1994_60"
    source := ⟨"dixon-1994", "§6.2.2 (60)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "yabu ŋuma-ŋgu giga-n bural-ŋa-ygu jaja-gu"
    glossedTokens := [("yabu", "mother.ABS"), ("ŋuma-ŋgu", "father-ERG"), ("giga-n", "tell.to.do-NONFUT"), ("bural-ŋa-ygu", "see-ANTIPASS-PURP"), ("jaja-gu", "child-DAT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "purposive"), ("first", "O"), ("second", "A"), ("derivation", "antipassive")] }

def ex_61 : LinguisticExample :=
  { id := "dixon1994_61"
    source := ⟨"dixon-1994", "§6.2.2 (61)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma banaga-ŋu yabu-ŋgu bura-n"
    glossedTokens := [("ŋuma", "father.ABS"), ("banaga-ŋu", "return-REL.ABS"), ("yabu-ŋgu", "mother-ERG"), ("bura-n", "see-NONFUT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "relative"), ("first", "O"), ("second", "S"), ("derivation", "none")] }

def ex_62 : LinguisticExample :=
  { id := "dixon1994_62"
    source := ⟨"dixon-1994", "§6.2.2 (62)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma yabu-ŋgu banaga-ŋu-rru bura-n"
    glossedTokens := [("ŋuma", "father.ABS"), ("yabu-ŋgu", "mother-ERG"), ("banaga-ŋu-rru", "return-REL-ERG"), ("bura-n", "see-NONFUT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "relative"), ("first", "A"), ("second", "S"), ("derivation", "none")] }

def ex_63 : LinguisticExample :=
  { id := "dixon1994_63"
    source := ⟨"dixon-1994", "§6.2.2 (63)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "yabu bural-ŋa-ŋu ŋuma-gu banaga-nyu"
    glossedTokens := [("yabu", "mother.ABS"), ("bural-ŋa-ŋu", "see-ANTIPASS-REL.ABS"), ("ŋuma-gu", "father-DAT"), ("banaga-nyu", "return-NONFUT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "relative"), ("first", "S"), ("second", "A"), ("derivation", "antipassive")] }

def ex_66 : LinguisticExample :=
  { id := "dixon1994_66"
    source := ⟨"dixon-1994", "§6.2.2 (66)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "yugu ŋuma-ŋgu balgal-ma-n yabu-gu"
    glossedTokens := [("yugu", "stick.ABS"), ("ŋuma-ŋgu", "father-ERG"), ("balgal-ma-n", "hit-INSTV-NONFUT"), ("yabu-gu", "mother-DAT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "instrumentive"), ("function", "O")] }

def ex_68 : LinguisticExample :=
  { id := "dixon1994_68"
    source := ⟨"dixon-1994", "§6.2.2 (68)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "yugu ŋuma-ŋgu balgal-ma-ŋu yabu-gu jaja-ŋgu bura-n"
    glossedTokens := [("yugu", "stick.ABS"), ("ŋuma-ŋgu", "father-ERG"), ("balgal-ma-ŋu", "hit-INSTV-REL.ABS"), ("yabu-gu", "mother-DAT"), ("jaja-ŋgu", "child-ERG"), ("bura-n", "see-NONFUT")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "relative"), ("first", "O"), ("second", "O"), ("derivation", "instrumentive")] }

def en_a : LinguisticExample :=
  { id := "dixon1994_en_a"
    source := ⟨"dixon-1994", "§6.2.1 (a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill entered and sat down."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "S"), ("second", "S"), ("derivation", "none")] }

def en_b : LinguisticExample :=
  { id := "dixon1994_en_b"
    source := ⟨"dixon-1994", "§6.2.1 (b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill entered and was seen by Fred."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "S"), ("second", "O"), ("derivation", "passive")] }

def en_c : LinguisticExample :=
  { id := "dixon1994_en_c"
    source := ⟨"dixon-1994", "§6.2.1 (c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill entered and saw Fred."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "S"), ("second", "A"), ("derivation", "none")] }

def en_d : LinguisticExample :=
  { id := "dixon1994_en_d"
    source := ⟨"dixon-1994", "§6.2.1 (d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill was seen by Fred and laughed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "O"), ("second", "S"), ("derivation", "passive")] }

def en_e : LinguisticExample :=
  { id := "dixon1994_en_e"
    source := ⟨"dixon-1994", "§6.2.1 (e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fred saw Bill and laughed."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "A"), ("second", "S"), ("derivation", "none")] }

def en_f : LinguisticExample :=
  { id := "dixon1994_en_f"
    source := ⟨"dixon-1994", "§6.2.1 (f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill was kicked by Tom and punched by Bob."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Tom kicked and Bob punched Bill.", .acceptable)]
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "O"), ("second", "O"), ("derivation", "passive")] }

def en_g : LinguisticExample :=
  { id := "dixon1994_en_g"
    source := ⟨"dixon-1994", "§6.2.1 (g)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bob kicked Jim and punched Bill."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "A"), ("second", "A"), ("derivation", "none")] }

def en_h : LinguisticExample :=
  { id := "dixon1994_en_h"
    source := ⟨"dixon-1994", "§6.2.1 (h)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bob was kicked by Tom and punched Bill."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "O"), ("second", "A"), ("derivation", "passive")] }

def en_i : LinguisticExample :=
  { id := "dixon1994_en_i"
    source := ⟨"dixon-1994", "§6.2.1 (i)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bob punched Bill and was kicked by Tom."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "A"), ("second", "O"), ("derivation", "passive")] }

def en_j : LinguisticExample :=
  { id := "dixon1994_en_j"
    source := ⟨"dixon-1994", "§6.2.1 (j)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fred punched and kicked Bill."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Fred punched Bill and kicked him.", .acceptable)]
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "A"), ("second", "A"), ("derivation", "none")] }

def en_k : LinguisticExample :=
  { id := "dixon1994_en_k"
    source := ⟨"dixon-1994", "§6.2.1 (k)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fred punched Bill and was kicked by him."
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := [("Fred punched and was kicked by Bill.", .acceptable)]
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "A"), ("second", "O"), ("derivation", "passive")] }

def all : List LinguisticExample := [ex_1_2_5, ex_1_2_7, ex_1_2_12, ex_15, ex_17, ex_19, ex_20, ex_21, ex_24, ex_28, ex_32, ex_33, ex_34, ex_36, ex_39, ex_42, ex_44, ex_46, ex_52, ex_56, ex_57, ex_59, ex_60, ex_61, ex_62, ex_63, ex_66, ex_68, en_a, en_b, en_c, en_d, en_e, en_f, en_g, en_h, en_i, en_j, en_k]

end Dixon1994.Examples
