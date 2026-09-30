module

public import Linglib.Data.Examples.Schema

/-!
# `Matthewson2016` — typed example data

Auto-generated from `Linglib/Data/Examples/Matthewson2016.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Matthewson2016.Examples`.
-/

@[expose] public section

namespace Matthewson2016.Examples

open Data.Examples

def ex25 : LinguisticExample :=
  { id := "matthewson2016_ex25"
    source := ⟨"matthewson-2016", "(25)"⟩
    reportedIn := none
    language := "lill1248"
    primaryText := "wá7=k'a ku=mám'teq láku7 áltsq7=a, t'u7 nílh=a cwílh=t'u7 ti=sk'éxem=a wa7 qan'ím-ens-an"
    glossedTokens := [("wá7=k'a", "be=INFER"), ("ku=mám'teq", "DET=walk"), ("láku7", "DEIC"), ("áltsq7=a", "outside=EXIS"), ("t'u7", "but"), ("nílh=a", "FOC=a"), ("cwílh=t'u7", "after.all=just"), ("ti=sk'éxem=a", "DET=wind=EXIS"), ("wa7", "IPFV"), ("qan'ím-ens-an", "hear-DIR-1SG.ERG")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "18.2.4"), ("modal", "k'a"), ("test", "deniability")] }

def ex26 : LinguisticExample :=
  { id := "matthewson2016_ex26"
    source := ⟨"matthewson-2016", "(26)"⟩
    reportedIn := none
    language := "lill1248"
    primaryText := "wa7 lákw7a ku=mám'teq láku7 áltsq7=a, t'u7 nílh=a cwílh=t'u7 ti=sk'éxem=a wa7 qan'ím-ens-an"
    glossedTokens := [("wa7", "be"), ("lákw7a", "SENS.NON.VIS"), ("ku=mám'teq", "DET=walk"), ("láku7", "DEIC"), ("áltsq7=a", "outside=EXIS"), ("t'u7", "but"), ("nílh=a", "FOC=a"), ("cwílh=t'u7", "after.all=just"), ("ti=sk'éxem=a", "DET=wind=EXIS"), ("wa7", "IPFV"), ("qan'ím-ens-an", "hear-DIR-1SG.ERG")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "18.2.4"), ("modal", "lákw7a"), ("test", "deniability")] }

def ex27 : LinguisticExample :=
  { id := "matthewson2016_ex27"
    source := ⟨"matthewson-2016", "(27)"⟩
    reportedIn := none
    language := "lill1248"
    primaryText := "t'ec=k'a=t'u7 ku=páoy, t'u7 áoz=t'u7 kw=a=s áma"
    glossedTokens := [("t'ec=k'a=t'u7", "tasty=INFER=just"), ("ku=páoy", "DET=pie"), ("t'u7", "but"), ("áoz=t'u7", "NEG=just"), ("kw=a=s", "DET=IPFV=3POSS"), ("áma", "good")]
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "18.2.4"), ("modal", "k'a"), ("test", "deniability")] }

def ex28 : LinguisticExample :=
  { id := "matthewson2016_ex28"
    source := ⟨"matthewson-2016", "(28)"⟩
    reportedIn := none
    language := "lill1248"
    primaryText := "t'éc=t'u7 lákw7a ku=páoy, t'u7 áoz=t'u7 kw=a=s áma"
    glossedTokens := [("t'éc=t'u7", "sweet=just"), ("lákw7a", "SENS.NON.VIS"), ("ku=páoy", "DET=pie"), ("t'u7", "but"), ("áoz=t'u7", "NEG=just"), ("kw=a=s", "DET=IPFV=3POSS"), ("áma", "good")]
    context := "It smelled as if the pie was good, but there was too much salt so it was actually horrible."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "18.2.4"), ("modal", "lákw7a"), ("test", "deniability")] }

def ex37 : LinguisticExample :=
  { id := "matthewson2016_ex37"
    source := ⟨"matthewson-2016", "(37)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=ima=hl dim ixw-t"
    glossedTokens := [("yugw=ima=hl", "IPFV=EPIS=CN"), ("dim", "PROSP"), ("ixw-t", "fish.with.line-3")]
    context := "You're wondering where your friend is. You notice his rod and tackle box are not in their usual place."
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .acceptable)]
    paperFeatures := [("section", "18.3.2"), ("modal", "ima('a)"), ("reportedFrom", "Peterson 2010, p. 161")] }

def ex38 : LinguisticExample :=
  { id := "matthewson2016_ex38"
    source := ⟨"matthewson-2016", "(38)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa=hl da'awhl ixw-t oo ligi nee=yimaa=dii ixw-t"
    glossedTokens := [("yugw=imaa=hl", "IPFV=EPIS=CN"), ("da'awhl", "then"), ("ixw-t", "fish-3II"), ("oo", "or"), ("ligi", "INDEF"), ("nee=yimaa=dii", "NEG=EPIS=CNTR"), ("ixw-t", "fish-3II")]
    context := "You thought your friend was fishing. But you see his rod and tackle box are still at his house. You really don't know if he's fishing or not."
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable)]
    paperFeatures := [("section", "18.3.2"), ("modal", "ima('a)"), ("reportedFrom", "Matthewson 2013a, p. 361")] }

def ex39 : LinguisticExample :=
  { id := "matthewson2016_ex39"
    source := ⟨"matthewson-2016", "(39)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "hi-wqíi-cix-∅ 'iléx̂ni hipt ke yox̂ hi-pá-ap-o'qa"
    glossedTokens := [("hi-wqíi-cix-∅", "3SUBJ-throw.away-IPFV.PL-PRES"), ("'iléx̂ni", "a.lot"), ("hipt", "food"), ("ke", "REL"), ("yox̂", "DEM"), ("hi-pá-ap-o'qa", "3SBJ-S.PL-eat-MOD")]
    context := "I am watching people clean out a cooler and throw away various things."
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .acceptable)]
    paperFeatures := [("section", "18.3.2"), ("modal", "o'qa"), ("downwardEntailing", "false"), ("reportedFrom", "Deal 2011, p. 574")] }

def ex40 : LinguisticExample :=
  { id := "matthewson2016_ex40"
    source := ⟨"matthewson-2016", "(40)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "hi-wqíi-cix-∅ 'óykala hipt ke yox̂ hi-pá-ap-o'qa"
    glossedTokens := [("hi-wqíi-cix-∅", "3SUBJ-throw.away-IPFV.PL-PRES"), ("'óykala", "all"), ("hipt", "food"), ("ke", "REL"), ("yox̂", "DEM"), ("hi-pá-ap-o'qa", "3SBJ-S.PL-eat-MOD")]
    context := "As in (39)."
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .unacceptable)]
    paperFeatures := [("section", "18.3.2"), ("modal", "o'qa"), ("downwardEntailing", "true"), ("reportedFrom", "Deal 2011, p. 574")] }

def ex42a : LinguisticExample :=
  { id := "matthewson2016_ex42a"
    source := ⟨"matthewson-2016", "(42a)"⟩
    reportedIn := none
    language := "okan1243"
    primaryText := "Mary mat ac-qíc-əlx"
    glossedTokens := [("Mary", "Mary"), ("mat", "MOD"), ("ac-qíc-əlx", "CUST-run-LEX")]
    context := "You know that Mary loves to go running and often goes on runs randomly. She could also be at the store or at school. I ask you, where is Mary?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "18.3.2"), ("modal", "mat"), ("force", "possibility"), ("reportedFrom", "Menzies 2013, p. 2")] }

def ex42b : LinguisticExample :=
  { id := "matthewson2016_ex42b"
    source := ⟨"matthewson-2016", "(42b)"⟩
    reportedIn := none
    language := "okan1243"
    primaryText := "Mary cmay ac-qíc-əlx"
    glossedTokens := [("Mary", "Mary"), ("cmay", "MOD"), ("ac-qíc-əlx", "CUST-run-LEX")]
    context := "You know that Mary loves to go running and often goes on runs randomly. She could also be at the store or at school. I ask you, where is Mary?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "18.3.2"), ("modal", "cmay"), ("force", "possibility"), ("reportedFrom", "Menzies 2013, p. 2")] }

def ex43a : LinguisticExample :=
  { id := "matthewson2016_ex43a"
    source := ⟨"matthewson-2016", "(43a)"⟩
    reportedIn := none
    language := "okan1243"
    primaryText := "Mary mat ac-qíc-əlx"
    glossedTokens := [("Mary", "Mary"), ("mat", "MOD"), ("ac-qíc-əlx", "CUST-run-LEX")]
    context := "Mary runs every day to train for a marathon. She usually runs at 6 pm on Tuesdays. Today is Tuesday and it's 6 pm. I ask you, where is Mary?"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "18.3.2"), ("modal", "mat"), ("force", "necessity"), ("reportedFrom", "Menzies 2013, p. 2")] }

def ex43b : LinguisticExample :=
  { id := "matthewson2016_ex43b"
    source := ⟨"matthewson-2016", "(43b)"⟩
    reportedIn := none
    language := "okan1243"
    primaryText := "Mary cmay ac-qíc-əlx"
    glossedTokens := [("Mary", "Mary"), ("cmay", "MOD"), ("ac-qíc-əlx", "CUST-run-LEX")]
    context := "Mary runs every day to train for a marathon. She usually runs at 6 pm on Tuesdays. Today is Tuesday and it's 6 pm. I ask you, where is Mary?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "18.3.2"), ("modal", "cmay"), ("force", "necessity"), ("reportedFrom", "Menzies 2013, p. 2")] }

def ex57 : LinguisticExample :=
  { id := "matthewson2016_ex57"
    source := ⟨"matthewson-2016", "(57)"⟩
    reportedIn := none
    language := "siks1238"
    primaryText := "matonni ni-maat-ssksini-'p-wa ot-aanist-a'pssi-wa piiksiksinaa-wa aahkam-omitaa-wa"
    glossedTokens := [("matonni", "yesterday"), ("ni-maat-ssksini-'p-wa", "1-NEG-know.VTI-LOC:0-NONAFF"), ("ot-aanist-a'pssi-wa", "3-manner-be.VAI-3"), ("piiksiksinaa-wa", "snake-3"), ("aahkam-omitaa-wa", "EPIS-dog-3")]
    context := "Stacey bought a bone for Pat's pet, thinking it might be a dog. Later, she finds out the pet is a snake. When Pat asks her why she bought a bone, she says:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "18.4.3"), ("flavor", "epistemic"), ("perspective", "past"), ("reportedFrom", "Louie 2012")] }

def ex58 : LinguisticExample :=
  { id := "matthewson2016_ex58"
    source := ⟨"matthewson-2016", "(58)"⟩
    reportedIn := none
    language := "kute1249"
    primaryText := "lin hin sa·nilxuʔ-ni"
    glossedTokens := [("lin", "EPIS"), ("hin", "2"), ("sa·nilxuʔ-ni", "sick-IND")]
    context := "Your neighbour doesn't show up for work and you know there's been a flu going around. You send your son to bring her hot soup. She actually took the day off because her apartment flooded, so she asks why you sent her soup in the middle of the day."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "18.4.3"), ("flavor", "epistemic"), ("perspective", "past"), ("reportedFrom", "Laturnus 2012")] }

def ex59 : LinguisticExample :=
  { id := "matthewson2016_ex59"
    source := ⟨"matthewson-2016", "(59)"⟩
    reportedIn := none
    language := "lill1248"
    primaryText := "kwís=k'a=tu7"
    glossedTokens := [("kwís=k'a=tu7", "rain=EPIS=then")]
    context := "When you looked out of your window earlier today the ground was wet, so it looked like it might have rained. But you find out later that sprinklers had been watering the ground."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "18.4.3"), ("modal", "k'a"), ("flavor", "epistemic"), ("perspective", "past")] }

def ex60 : LinguisticExample :=
  { id := "matthewson2016_ex60"
    source := ⟨"matthewson-2016", "(60)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa=hl wis da'awhl"
    glossedTokens := [("yugw=imaa=hl", "IPFV=EPIS=CN"), ("wis", "rain"), ("da'awhl", "then")]
    context := "When you looked out your window earlier today, the ground was wet, so it looked like it might have rained. But you found out later that the sprinklers had been watering the ground."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "18.4.3"), ("modal", "ima('a)"), ("perspective", "past"), ("orientation", "past"), ("prospective", "false"), ("reportedFrom", "Matthewson 2013a, p. 366")] }

def ex61 : LinguisticExample :=
  { id := "matthewson2016_ex61"
    source := ⟨"matthewson-2016", "(61)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa=hl wis da'awhl"
    glossedTokens := [("yugw=imaa=hl", "IPFV=EPIS=CN"), ("wis", "rain"), ("da'awhl", "then")]
    context := "When you looked out your window earlier today, water was falling, so it looked like it was raining. But you found out later it was the gutters leaking."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "18.4.3"), ("modal", "ima('a)"), ("perspective", "past"), ("orientation", "present"), ("prospective", "false"), ("reportedFrom", "Matthewson 2013a, p. 363")] }

def ex62 : LinguisticExample :=
  { id := "matthewson2016_ex62"
    source := ⟨"matthewson-2016", "(62)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa=hl dim wis"
    glossedTokens := [("yugw=imaa=hl", "IPFV=EPIS=CN"), ("dim", "PROSP"), ("wis", "rain")]
    context := "This morning you looked out your window and judging by the clouds, it looked like it might have been going to rain, so you took your raincoat. Later you're explaining to me why you did that."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "18.4.3"), ("modal", "ima('a)"), ("perspective", "past"), ("orientation", "future"), ("prospective", "true"), ("reportedFrom", "Matthewson 2013a, p. 366")] }

def ex63a : LinguisticExample :=
  { id := "matthewson2016_ex63a"
    source := ⟨"matthewson-2016", "(63a)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa=hl wis"
    glossedTokens := [("yugw=imaa=hl", "IPFV=EPIS=CN"), ("wis", "rain")]
    context := "You see puddles, and the flowers looking fresh and damp."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "18.4.3"), ("modal", "ima('a)"), ("orientation", "past"), ("prospective", "false"), ("reportedFrom", "Matthewson 2013a, pp. 364–365")] }

def ex63b : LinguisticExample :=
  { id := "matthewson2016_ex63b"
    source := ⟨"matthewson-2016", "(63b)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa=hl wis"
    glossedTokens := [("yugw=imaa=hl", "IPFV=EPIS=CN"), ("wis", "rain")]
    context := "You hear pattering on the roof."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "18.4.3"), ("modal", "ima('a)"), ("orientation", "present"), ("prospective", "false"), ("reportedFrom", "Matthewson 2013a, pp. 364–365")] }

def ex63c : LinguisticExample :=
  { id := "matthewson2016_ex63c"
    source := ⟨"matthewson-2016", "(63c)"⟩
    reportedIn := none
    language := "gitx1241"
    primaryText := "yugw=imaa=hl wis"
    glossedTokens := [("yugw=imaa=hl", "IPFV=EPIS=CN"), ("wis", "rain")]
    context := "You hear thunder, so you think it might rain soon."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "18.4.3"), ("modal", "ima('a)"), ("orientation", "future"), ("prospective", "false"), ("reportedFrom", "Matthewson 2013a, pp. 364–365")] }

def ex64 : LinguisticExample :=
  { id := "matthewson2016_ex64"
    source := ⟨"matthewson-2016", "(64)"⟩
    reportedIn := none
    language := "niue1239"
    primaryText := "liga kua fano tei"
    glossedTokens := [("liga", "EPIS"), ("kua", "PRF"), ("fano", "go"), ("tei", "PRF")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "18.5"), ("modal", "liga"), ("force", "weak"), ("flavor", "epistemic"), ("reportedFrom", "Matthewson et al. 2012, p. 224")] }

def ex65 : LinguisticExample :=
  { id := "matthewson2016_ex65"
    source := ⟨"matthewson-2016", "(65)"⟩
    reportedIn := none
    language := "niue1239"
    primaryText := "Hī ika a Tom he aho nei ... liga malolo a ia"
    glossedTokens := [("Hī", "catch.fish"), ("ika", "fish"), ("a", "ABS"), ("Tom", "Tom"), ("he", "on"), ("aho", "day"), ("nei", "this"), ("liga", "EPIS"), ("malolo", "strong"), ("a", "ABS"), ("ia", "3SG")]
    context := "Tom wasn't fishing yesterday, and you were wondering about his health. But today you see him fishing."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "18.5"), ("modal", "liga"), ("flavor", "epistemic"), ("reportedFrom", "Matthewson et al. 2012, p. 228")] }

def ex66 : LinguisticExample :=
  { id := "matthewson2016_ex66"
    source := ⟨"matthewson-2016", "(66)"⟩
    reportedIn := none
    language := "niue1239"
    primaryText := "ne liga kua veli hifo e tama ke he pelapela"
    glossedTokens := [("ne", "PAST"), ("liga", "EPIS"), ("kua", "PRF"), ("veli", "fall"), ("hifo", "down"), ("e", "ABS"), ("tama", "child"), ("ke", "to"), ("he", ""), ("pelapela", "mud")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "18.5"), ("modal", "liga"), ("force", "strong"), ("flavor", "epistemic"), ("reportedFrom", "Seiter 1980, p. 13")] }

def ex67 : LinguisticExample :=
  { id := "matthewson2016_ex67"
    source := ⟨"matthewson-2016", "(67)"⟩
    reportedIn := none
    language := "niue1239"
    primaryText := "kua maeke he tama ia ke taute pasikala afi"
    glossedTokens := [("kua", "PRF"), ("maeke", "CIRC.POSSIB"), ("he", "at"), ("tama", "child"), ("ia", "that"), ("ke", "SBJ"), ("taute", "fix"), ("pasikala", "bicycle"), ("afi", "fire")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "18.5"), ("modal", "maeke"), ("force", "weak"), ("flavor", "circumstantial"), ("reportedFrom", "Seiter 1980, p. 140")] }

def ex68 : LinguisticExample :=
  { id := "matthewson2016_ex68"
    source := ⟨"matthewson-2016", "(68)"⟩
    reportedIn := none
    language := "niue1239"
    primaryText := "lata ke ō a tautolu he aho nei ki Queen Street"
    glossedTokens := [("lata", "CIRC.NECESS"), ("ke", "SBJ"), ("ō", "go.PL"), ("a", "ABS"), ("tautolu", "we.PL.INCL"), ("he", "on"), ("aho", "day"), ("nei", "this"), ("ki", "to"), ("Queen", "Queen"), ("Street", "Street")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "18.5"), ("modal", "lata"), ("force", "strong"), ("flavor", "deontic"), ("reportedFrom", "Seiter 1980, p. 133")] }

def all : List LinguisticExample := [ex25, ex26, ex27, ex28, ex37, ex38, ex39, ex40, ex42a, ex42b, ex43a, ex43b, ex57, ex58, ex59, ex60, ex61, ex62, ex63a, ex63b, ex63c, ex64, ex65, ex66, ex67, ex68]

end Matthewson2016.Examples
