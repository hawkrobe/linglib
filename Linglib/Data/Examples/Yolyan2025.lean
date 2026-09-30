module

public import Linglib.Data.Examples.Schema

/-!
# `Yolyan2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Yolyan2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Yolyan2025.Examples`.
-/

@[expose] public section

namespace Yolyan2025.Examples

open Data.Examples

def ex_2_11a_1 : Datum :=
  { id := "yolyan2025_2_11a_1"
    source := ⟨"yolyan-2025", "Example 2.11 (a)"⟩
    reportedIn := none
    language := "bemb1257"
    primaryText := "bá-ká-fík-á"
    glossedTokens := [("bá", "they"), ("ká", "FUT"), ("fík", "arrive"), ("á", "FV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("underlying_form", "/bá-ka-fik-a/"), ("spreading", "unbounded"), ("tone_skeleton_input", "HLLL"), ("tone_skeleton_output", "HHHH")] }

def ex_2_11a_2 : Datum :=
  { id := "yolyan2025_2_11a_2"
    source := ⟨"yolyan-2025", "Example 2.11 (a)"⟩
    reportedIn := none
    language := "bemb1257"
    primaryText := "bá-ká-mú-lóndólól-á"
    glossedTokens := [("bá", "they"), ("ká", "FUT"), ("mú", "him/her"), ("lóndólól", "introduce"), ("á", "FV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("underlying_form", "/bá-ka-mu-londolol-a/"), ("spreading", "unbounded")] }

def ex_2_11b_1 : Datum :=
  { id := "yolyan2025_2_11b_1"
    source := ⟨"yolyan-2025", "Example 2.11 (b)"⟩
    reportedIn := none
    language := "bemb1257"
    primaryText := "bá-ká-pát-à kó"
    glossedTokens := [("bá", "they"), ("ká", "FUT"), ("pát", "hate"), ("à", "FV"), ("kó", "kó")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("underlying_form", "/bá-ka-pat-a kó/"), ("spreading", "bounded"), ("tone_skeleton_input", "HLLLH"), ("tone_skeleton_output", "HHHLH")] }

def ex_2_11b_2 : Datum :=
  { id := "yolyan2025_2_11b_2"
    source := ⟨"yolyan-2025", "Example 2.11 (b)"⟩
    reportedIn := none
    language := "bemb1257"
    primaryText := "bá-ká-ló-òndòlòl-à kó"
    glossedTokens := [("bá", "they"), ("ká", "FUT"), ("ló", "introduce"), ("òndòlòl", "introduce"), ("à", "FV"), ("kó", "kó")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("underlying_form", "/bá-ka-londolol-a kó/"), ("spreading", "bounded")] }

def ex_2_11c : Datum :=
  { id := "yolyan2025_2_11c"
    source := ⟨"yolyan-2025", "Example 2.11 (c)"⟩
    reportedIn := none
    language := "bemb1257"
    primaryText := "ù-kù-tùl-à"
    glossedTokens := [("ù", "INF"), ("kù", "INF"), ("tùl", "pierce"), ("à", "FV")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("underlying_form", "/u-ku-tul-a/"), ("spreading", "none"), ("tone_skeleton_input", "LLLL"), ("tone_skeleton_output", "LLLL")] }

def ex_2_12a_1 : Datum :=
  { id := "yolyan2025_2_12a_1"
    source := ⟨"yolyan-2025", "Example 2.12 (a)"⟩
    reportedIn := none
    language := "nyan1302"
    primaryText := "bu-tí-ʃē"
    glossedTokens := [("bu", "1P"), ("tí", "NEG"), ("ʃē", "grow")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root_atr", "+"), ("blocking", "none")] }

def ex_2_12a_2 : Datum :=
  { id := "yolyan2025_2_12a_2"
    source := ⟨"yolyan-2025", "Example 2.12 (a)"⟩
    reportedIn := none
    language := "nyan1302"
    primaryText := "e-tí-be-ʃē"
    glossedTokens := [("e", "3S"), ("tí", "NEG"), ("be", "FUT"), ("ʃē", "grow")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root_atr", "+"), ("blocking", "none")] }

def ex_2_12b_1 : Datum :=
  { id := "yolyan2025_2_12b_1"
    source := ⟨"yolyan-2025", "Example 2.12 (b)"⟩
    reportedIn := none
    language := "nyan1302"
    primaryText := "bʊ-tɪ́-bá"
    glossedTokens := [("bʊ", "1P"), ("tɪ́", "NEG"), ("bá", "come")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root_atr", "-"), ("blocking", "none")] }

def ex_2_12b_2 : Datum :=
  { id := "yolyan2025_2_12b_2"
    source := ⟨"yolyan-2025", "Example 2.12 (b)"⟩
    reportedIn := none
    language := "nyan1302"
    primaryText := "a-tɪ́-ba-bá"
    glossedTokens := [("a", "3S"), ("tɪ́", "NEG"), ("ba", "FUT"), ("bá", "come")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root_atr", "-"), ("blocking", "none")] }

def ex_2_12c_1 : Datum :=
  { id := "yolyan2025_2_12c_1"
    source := ⟨"yolyan-2025", "Example 2.12 (c)"⟩
    reportedIn := none
    language := "nyan1302"
    primaryText := "i-tí-wu"
    glossedTokens := [("i", "1S"), ("tí", "NEG"), ("wu", "climb")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root_atr", "+"), ("blocking", "none"), ("initial_high", "yes")] }

def ex_2_12c_2 : Datum :=
  { id := "yolyan2025_2_12c_2"
    source := ⟨"yolyan-2025", "Example 2.12 (c)"⟩
    reportedIn := none
    language := "nyan1302"
    primaryText := "ɪ-ba-wu"
    glossedTokens := [("ɪ", "1S"), ("ba", "FUT"), ("wu", "climb")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root_atr", "+"), ("blocking", "conditional"), ("initial_high", "yes")] }

def ex_2_12c_3 : Datum :=
  { id := "yolyan2025_2_12c_3"
    source := ⟨"yolyan-2025", "Example 2.12 (c)"⟩
    reportedIn := none
    language := "nyan1302"
    primaryText := "ɪ-tɪ́-ka-a-ba-ba-wu"
    glossedTokens := [("ɪ", "1S"), ("tɪ́", "NEG"), ("ka", "PFV"), ("a", "PROG"), ("ba", "VENT"), ("ba", "VENT"), ("wu", "climb")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root_atr", "+"), ("blocking", "conditional"), ("initial_high", "yes")] }

def ex_2_12c_4 : Datum :=
  { id := "yolyan2025_2_12c_4"
    source := ⟨"yolyan-2025", "Example 2.12 (c)"⟩
    reportedIn := none
    language := "nyan1302"
    primaryText := "e-tí-ke-e-be-be-wu"
    glossedTokens := [("e", "3S"), ("tí", "NEG"), ("ke", "PFV"), ("e", "PROG"), ("be", "VENT"), ("be", "VENT"), ("wu", "climb")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root_atr", "+"), ("blocking", "none"), ("initial_high", "no")] }

def all : List Datum := [ex_2_11a_1, ex_2_11a_2, ex_2_11b_1, ex_2_11b_2, ex_2_11c, ex_2_12a_1, ex_2_12a_2, ex_2_12b_1, ex_2_12b_2, ex_2_12c_1, ex_2_12c_2, ex_2_12c_3, ex_2_12c_4]

end Yolyan2025.Examples
