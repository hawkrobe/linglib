module

public import Linglib.Data.Examples.Schema

/-!
# `Bobaljik2000` — typed example data

Auto-generated from `Linglib/Data/Examples/Bobaljik2000.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Bobaljik2000.Examples`.
-/

@[expose] public section

namespace Bobaljik2000.Examples

open Data.Examples

def ex_9a : Datum :=
  { id := "bobaljik2000_9a"
    source := ⟨"bobaljik-2000", "(9a)"⟩
    reportedIn := none
    language := "itel1242"
    primaryText := "t’-kzu-s-cen"
    glossedTokens := [("t’-kzu-s-cen", "1S:SU-help-PRES-1>3P:OB")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "kzu"), ("rootClass", "I"), ("subj", "1sg"), ("obj", "3pl"), ("m1", "t"), ("m2", "kzu"), ("m3", "s"), ("m4", "cen")] }

def ex_9b : Datum :=
  { id := "bobaljik2000_9b"
    source := ⟨"bobaljik-2000", "(9b)"⟩
    reportedIn := none
    language := "itel1242"
    primaryText := "t-t-s-ki-cen"
    glossedTokens := [("t-t-s-ki-cen", "1S:SU-bring-PRES-II-1>3P:OB")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "t"), ("rootClass", "II"), ("subj", "1sg"), ("obj", "3pl"), ("m1", "t"), ("m2", "t"), ("m3", "s"), ("m4", "ki"), ("m5", "cen")] }

def ex_10a : Datum :=
  { id := "bobaljik2000_10a"
    source := ⟨"bobaljik-2000", "(10a)"⟩
    reportedIn := none
    language := "itel1242"
    primaryText := "lcqu-z-in"
    glossedTokens := [("lcqu-z-in", "see-PRES-2S>3S:OB")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "lcqu"), ("rootClass", "I"), ("subj", "2sg"), ("obj", "3sg"), ("m1", "lcqu"), ("m2", "s"), ("m3", "in")] }

def ex_10b : Datum :=
  { id := "bobaljik2000_10b"
    source := ⟨"bobaljik-2000", "(10b)"⟩
    reportedIn := none
    language := "itel1242"
    primaryText := "t-s-c-in"
    glossedTokens := [("t-s-c-in", "bring-PRES-II-2S>3S:OB")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("root", "t"), ("rootClass", "II"), ("subj", "2sg"), ("obj", "3sg"), ("m1", "t"), ("m2", "s"), ("m3", "c"), ("m4", "in")] }

def all : List Datum := [ex_9a, ex_9b, ex_10a, ex_10b]

end Bobaljik2000.Examples
