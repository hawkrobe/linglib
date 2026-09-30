module

public import Linglib.Data.Examples.Schema

/-!
# `Scott2023` — typed example data

Auto-generated from `Linglib/Data/Examples/Scott2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Scott2023.Examples`.
-/

@[expose] public section

namespace Scott2023.Examples

open Data.Examples

def ex_78a : Datum :=
  { id := "scott2023_78a"
    source := ⟨"scott-2023", "(78a)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma qo b'et *qo'=y."
    glossedTokens := [("Ma", "PROX"), ("qo", "B1PL"), ("b'et", "walk"), ("qo'=y", "1PL=DISAGR")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("position", "S"), ("cell", "1plExcl"), ("morphemes", "qo=i")] }

def ex_78b : Datum :=
  { id := "scott2023_78b"
    source := ⟨"scott-2023", "(78b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma ∅ kub' q-tz'ib'-an *qo'=y."
    glossedTokens := [("Ma", "PROX"), ("∅", "B2/3SG"), ("kub'", "DIR:down"), ("q-tz'ib'-an", "A1PL-write-DS"), ("qo'=y", "1PL=DISAGR")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("position", "A"), ("cell", "1plExcl"), ("morphemes", "qo=i")] }

def ex_78c : Datum :=
  { id := "scott2023_78c"
    source := ⟨"scott-2023", "(78c)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "q-lan *qo'=y"
    glossedTokens := [("q-lan", "A1PL-wool.thread"), ("qo'=y", "1PL=DISAGR")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("position", "possessor"), ("cell", "1plExcl"), ("morphemes", "qo=i")] }

def ex_79 : Datum :=
  { id := "scott2023_79"
    source := ⟨"scott-2023", "(79)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "B'et qo'=y."
    glossedTokens := [("B'et", "walk"), ("qo'=y", "1PL=DISAGR")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "unagreed"), ("cell", "1plExcl"), ("morphemes", "qo=i")] }

def ex_68b : Datum :=
  { id := "scott2023_68b"
    source := ⟨"scott-2023", "(68b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "O qo tan=i."
    glossedTokens := [("O", "PFV"), ("qo", "B1PL"), ("tan", "sleep"), ("=i", "=DISAGR")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "S"), ("cell", "1plExcl"), ("morphemes", "=i")] }

def ex_85a : Datum :=
  { id := "scott2023_85a"
    source := ⟨"scott-2023", "(85a)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma chin b'et *qin=i."
    glossedTokens := [("Ma", "PROX"), ("chin", "B1SG"), ("b'et", "walk"), ("qin=i", "1SG=DISAGR")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("position", "S"), ("cell", "1sg"), ("morphemes", "qin=i")] }

def ex_85b : Datum :=
  { id := "scott2023_85b"
    source := ⟨"scott-2023", "(85b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma ∅ kub' n-tz'ib'-an *qin=i."
    glossedTokens := [("Ma", "PROX"), ("∅", "B2/3SG"), ("kub'", "DIR:down"), ("n-tz'ib'-an", "A1SG-write-DS"), ("qin=i", "1SG=DISAGR")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("position", "A"), ("cell", "1sg"), ("morphemes", "qin=i")] }

def ex_85c : Datum :=
  { id := "scott2023_85c"
    source := ⟨"scott-2023", "(85c)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "n-lan *qin=i"
    glossedTokens := [("n-lan", "A1SG-wool.thread"), ("qin=i", "1SG=DISAGR")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("position", "possessor"), ("cell", "1sg"), ("morphemes", "qin=i")] }

def ex_62 : Datum :=
  { id := "scott2023_62"
    source := ⟨"scott-2023", "(62)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma chin b'et=i."
    glossedTokens := [("Ma", "PROX"), ("chin", "B1SG"), ("b'et", "walk"), ("=i", "=DISAGR")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "S"), ("cell", "1sg"), ("morphemes", "=i")] }

def ex_86a : Datum :=
  { id := "scott2023_86a"
    source := ⟨"scott-2023", "(86a)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma chi b'et q=i."
    glossedTokens := [("Ma", "PROX"), ("chi", "B2/3PL"), ("b'et", "walk"), ("q=i", "2PL=DISAGR")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "S"), ("cell", "2pl"), ("morphemes", "q=i")] }

def ex_86b : Datum :=
  { id := "scott2023_86b"
    source := ⟨"scott-2023", "(86b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma ∅ kub' ky-tz'ib'-an q=i."
    glossedTokens := [("Ma", "PROX"), ("∅", "B2/3SG"), ("kub'", "DIR:down"), ("ky-tz'ib'-an", "A2/3PL-write-DS"), ("q=i", "2PL=DISAGR")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "A"), ("cell", "2pl"), ("morphemes", "q=i")] }

def ex_86c : Datum :=
  { id := "scott2023_86c"
    source := ⟨"scott-2023", "(86c)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "ky-lan q=i"
    glossedTokens := [("ky-lan", "A2/3PL-wool.thread"), ("q=i", "2PL=DISAGR")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "possessor"), ("cell", "2pl"), ("morphemes", "q=i")] }

def ex_87a : Datum :=
  { id := "scott2023_87a"
    source := ⟨"scott-2023", "(87a)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma chi b'et qa."
    glossedTokens := [("Ma", "PROX"), ("chi", "B2/3PL"), ("b'et", "walk"), ("qa", "PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "S"), ("cell", "3pl"), ("morphemes", "qa")] }

def ex_87b : Datum :=
  { id := "scott2023_87b"
    source := ⟨"scott-2023", "(87b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma ∅ kub' ky-tz'ib'-an qa."
    glossedTokens := [("Ma", "PROX"), ("∅", "B2/3SG"), ("kub'", "DIR:down"), ("ky-tz'ib'-an", "A2/3PL-write-DS"), ("qa", "PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "A"), ("cell", "3pl"), ("morphemes", "qa")] }

def ex_87c : Datum :=
  { id := "scott2023_87c"
    source := ⟨"scott-2023", "(87c)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "ky-lan qa"
    glossedTokens := [("ky-lan", "A2/3PL-wool.thread"), ("qa", "PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "possessor"), ("cell", "3pl"), ("morphemes", "qa")] }

def ex_88b : Datum :=
  { id := "scott2023_88b"
    source := ⟨"scott-2023", "(88b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "B'et qin=i."
    glossedTokens := [("B'et", "walk"), ("qin=i", "1SG=DISAGR")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "unagreed"), ("cell", "1sg"), ("morphemes", "qin=i")] }

def ex_88c : Datum :=
  { id := "scott2023_88c"
    source := ⟨"scott-2023", "(88c)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "B'et q=i."
    glossedTokens := [("B'et", "walk"), ("q=i", "2PL=DISAGR")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "unagreed"), ("cell", "2pl"), ("morphemes", "q=i")] }

def ex_88d : Datum :=
  { id := "scott2023_88d"
    source := ⟨"scott-2023", "(88d)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "B'et qa."
    glossedTokens := [("B'et", "walk"), ("qa", "PL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "unagreed"), ("cell", "3pl"), ("morphemes", "qa")] }

def ex_69a : Datum :=
  { id := "scott2023_69a"
    source := ⟨"scott-2023", "(69a)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma tz'=ok ky-ke'y-an qa qin=i."
    glossedTokens := [("Ma", "PROX"), ("tz'=ok", "B2/3SG=DIR:in"), ("ky-ke'y-an", "A2/3PL-see-DS"), ("qa", "PL"), ("qin=i", "1SG=DISAGR")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "object"), ("cell", "1sg"), ("morphemes", "qin=i")] }

def ex_89a : Datum :=
  { id := "scott2023_89a"
    source := ⟨"scott-2023", "(89a)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "ky-ja q=i"
    glossedTokens := [("ky-ja", "A2/3PL-house"), ("q=i", "2PL=DISAGR")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "possessor"), ("cell", "2pl"), ("morphemes", "q=i")] }

def ex_89b : Datum :=
  { id := "scott2023_89b"
    source := ⟨"scott-2023", "(89b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "ky-ja=y"
    glossedTokens := [("ky-ja", "A2/3PL-house"), ("=y", "=DISAGR")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "possessor"), ("cell", "2pl"), ("morphemes", "=i"), ("optionalReduction", "yes")] }

def ex_90b : Datum :=
  { id := "scott2023_90b"
    source := ⟨"scott-2023", "(90b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma ∅ tzaj ky-q'ama-'n=i w-i=y."
    glossedTokens := [("Ma", "PROX"), ("∅", "B2/3SG"), ("tzaj", "DIR:come"), ("ky-q'ama-'n", "A2/3PL-tell-DS"), ("=i", "=DISAGR"), ("w-i=y", "A1SG-RN:dat=DISAGR")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "A"), ("cell", "2pl"), ("morphemes", "=i"), ("optionalReduction", "yes")] }

def ex_91a : Datum :=
  { id := "scott2023_91a"
    source := ⟨"scott-2023", "(91a)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma chi b'ix-an q=i."
    glossedTokens := [("Ma", "PROX"), ("chi", "B2/3PL"), ("b'ix-an", "dance-DS"), ("q=i", "2PL=DISAGR")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "S"), ("cell", "2pl"), ("morphemes", "q=i")] }

def ex_91b : Datum :=
  { id := "scott2023_91b"
    source := ⟨"scott-2023", "(91b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "#Ma chi b'ix-n=i."
    glossedTokens := [("Ma", "PROX"), ("chi", "B2/3PL"), ("b'ix-n", "dance-DS"), ("=i", "=DISAGR")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "S"), ("cell", "2pl"), ("morphemes", "=i")] }

def ex_57 : Datum :=
  { id := "scott2023_57"
    source := ⟨"scott-2023", "(57)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma chn=ok t-ke'y-an Mintz."
    glossedTokens := [("Ma", "PROX"), ("chn=ok", "B1SG=DIR:in"), ("t-ke'y-an", "A2/3SG-see-DS"), ("Mintz", "Mintz")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "agreeingObject"), ("cell", "1sg"), ("setB", "chin")] }

def ex_59 : Datum :=
  { id := "scott2023_59"
    source := ⟨"scott-2023", "(59)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma tz'=ok t-ke'y-an Mintz qin=i."
    glossedTokens := [("Ma", "PROX"), ("tz'=ok", "B2/3SG=DIR:in"), ("t-ke'y-an", "A2/3SG-see-DS"), ("Mintz", "Mintz"), ("qin=i", "1SG=DISAGR")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "defaultObject"), ("cell", "1sg"), ("setB", "tz'")] }

def ex_73 : Datum :=
  { id := "scott2023_73"
    source := ⟨"scott-2023", "(73)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Taj w-ul=i …"
    glossedTokens := [("Taj", "when"), ("w-ul", "A1SG-arrive"), ("=i", "=DISAGR")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "superExtendedErgative"), ("position", "S"), ("cell", "1sg"), ("setA", "w")] }

def ex_77a : Datum :=
  { id := "scott2023_77a"
    source := ⟨"scott-2023", "(77a)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Taj t-ok t-ke'y-an=i qin=i …"
    glossedTokens := [("Taj", "when"), ("t-ok", "A2/3SG-DIR:in"), ("t-ke'y-an", "A2/3SG-see-DS"), ("=i", "=DISAGR"), ("qin=i", "1SG=DISAGR")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "superExtendedErgative"), ("position", "object"), ("cell", "1sg"), ("setA", "t")] }

def ex_77b : Datum :=
  { id := "scott2023_77b"
    source := ⟨"scott-2023", "(77b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "*Taj w-ok t-ke'y-an=i …"
    glossedTokens := [("Taj", "when"), ("w-ok", "A1SG-DIR:in"), ("t-ke'y-an", "A2/3SG-see-DS"), ("=i", "=DISAGR")]
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "superExtendedErgative"), ("position", "object"), ("cell", "1sg"), ("setA", "w")] }

def all : List Datum := [ex_78a, ex_78b, ex_78c, ex_79, ex_68b, ex_85a, ex_85b, ex_85c, ex_62, ex_86a, ex_86b, ex_86c, ex_87a, ex_87b, ex_87c, ex_88b, ex_88c, ex_88d, ex_69a, ex_89a, ex_89b, ex_90b, ex_91a, ex_91b, ex_57, ex_59, ex_73, ex_77a, ex_77b]

end Scott2023.Examples
