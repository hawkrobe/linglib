module

public import Linglib.Data.Examples.Schema

/-!
# `MocnikAbramovitz2019` — typed example data

Auto-generated from `Linglib/Data/Examples/MocnikAbramovitz2019.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace MocnikAbramovitz2019.Examples`.
-/

@[expose] public section

namespace MocnikAbramovitz2019.Examples

open Data.Examples

def ex2 : LinguisticExample :=
  { id := "mocnikabramovitz2019_ex2"
    source := ⟨"mocnik-abramovitz-2019", "(2)"⟩
    reportedIn := none
    language := "kory1246"
    primaryText := "meʎʎo kivəŋ, əno kumuqetəŋ"
    discourseSegments := []
    glossedTokens := [("meʎʎo", "Melljo"), ("kivəŋ", "ivək.3SG.PRS"), ("əno", "that"), ("kumuqetəŋ", "rain.3SG.PRS")]
    translation := "Melljo says that it's raining."
    context := ""
    judgment := .acceptable
    alternatives := [("meʎʎo kivəŋ, kumuqetəŋ", .acceptable)]
    readings := [("says", .acceptable), ("thinks", .acceptable), ("allows", .acceptable), ("hopes", .acceptable), ("fears", .acceptable), ("knows", .unacceptable), ("imagines", .unacceptable), ("wishes", .unacceptable)]
    paperFeatures := [("section", "1")]
    comment := "The complementizer əno is optional. 'wish' needs the counterfactual prefix ʔ- in the embedded clause, (3)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex4 : LinguisticExample :=
  { id := "mocnikabramovitz2019_ex4"
    source := ⟨"mocnik-abramovitz-2019", "(4)"⟩
    reportedIn := none
    language := "kory1246"
    primaryText := "qoo. təkivəŋ əno kotavareɲjaŋəŋ jajak. qoo. təkivəŋ əno keluŋ umkək."
    discourseSegments := ["qoo. təkivəŋ əno kotavareɲjaŋəŋ jajak.", "qoo. təkivəŋ əno keluŋ umkək."]
    glossedTokens := [("qoo", "dunno"), ("təkivəŋ", "ivək.1SG.PRS"), ("əno", "that"), ("kotavareɲjaŋəŋ", "make.jam.3SG.PRS"), ("jajak", "at.home"), ("qoo", "dunno"), ("təkivəŋ", "ivək.1SG.PRS"), ("əno", "that"), ("keluŋ", "pick.berries.3SG.PRS"), ("umkək", "in.forest")]
    translation := "I don't know. I allow for the possibility that she's making jam at home. I don't know. I allow for the possibility that she's in the forest picking berries."
    context := "Hewngyto is walking down the street. Melljo sees him and asks: 'Where is your wife? Is she making jam at home?' He replies with the first sentence. He continues walking. Qechghylqot sees him and asks: 'Where is your wife? Is she picking berries in the forest?' Hewngyto replies with the second."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2")]
    comment := "The speaker first rejected the discourse and accepted it once asked whether ivək could mean dopuskat' 'allow for the possibility' (§1.1)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex5 : LinguisticExample :=
  { id := "mocnikabramovitz2019_ex5"
    source := ⟨"mocnik-abramovitz-2019", "(5)"⟩
    reportedIn := none
    language := "kory1246"
    primaryText := "ʔewŋəto kolmalavəŋ əno kumuqetəŋ, ʔam ʔopta kolmalavəŋ əno ujŋe emuqetke."
    discourseSegments := []
    glossedTokens := [("ʔewŋəto", "H."), ("kolmalavəŋ", "believe.3SG.PRS"), ("əno", "that"), ("kumuqetəŋ", "rain.PRS"), ("ʔam", "but"), ("ʔopta", "also"), ("kolmalavəŋ", "believe.3SG.PRS"), ("əno", "that"), ("ujŋe", "NEG"), ("emuqetke", "rain")]
    translation := "Hewngyto allows that it is raining but also allows that it is not raining."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2")]
    comment := "Intended translation. The verb is ləmalavək 'believe', which has no possibility reading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex6 : LinguisticExample :=
  { id := "mocnikabramovitz2019_ex6"
    source := ⟨"mocnik-abramovitz-2019", "(6)"⟩
    reportedIn := none
    language := "kory1246"
    primaryText := "ʔewŋəto kivəŋ əno kumuqetəŋ, ʔam ʔopta kivəŋ əno ujŋe emuqetke."
    discourseSegments := []
    glossedTokens := [("ʔewŋəto", "H."), ("kivəŋ", "ivək.3SG.PRS"), ("əno", "that"), ("kumuqetəŋ", "rain.3SG.PRS"), ("ʔam", "but"), ("ʔopta", "also"), ("kivəŋ", "ivək.3SG.PRS"), ("əno", "that"), ("ujŋe", "NEG"), ("emuqetke", "rain")]
    translation := "Hewngyto allows that it is raining but also allows that it is not raining."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex7 : LinguisticExample :=
  { id := "mocnikabramovitz2019_ex7"
    source := ⟨"mocnik-abramovitz-2019", "(7)"⟩
    reportedIn := none
    language := "kory1246"
    primaryText := "əməŋ ʔujemtewilʔu mekiw ewlaj əno jemuqetiki nejetən muqeičʔən"
    discourseSegments := []
    glossedTokens := [("əməŋ", "all"), ("ʔujemtewilʔu", "people"), ("mekiw", "who"), ("ewlaj", "ivək.3PL.PRS"), ("əno", "that"), ("jemuqetiki", "rain.FUT.IPFV"), ("nejetən", "bring.3PL>3SG.PST"), ("muqeičʔən", "raincoat")]
    translation := "Everybody who said that it will rain brought a raincoat."
    context := "We're walking down the street and there are many people with raincoats. Melljo says:"
    judgment := .acceptable
    alternatives := []
    readings := [("said", .acceptable), ("allowed", .acceptable)]
    paperFeatures := [("section", "2")]
    comment := "The 'said' translation was volunteered and the 'allowed' one accepted in a matching task."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex8a : LinguisticExample :=
  { id := "mocnikabramovitz2019_ex8a"
    source := ⟨"mocnik-abramovitz-2019", "(8a)"⟩
    reportedIn := none
    language := "kory1246"
    primaryText := "təkivəŋ əno əɲɲin qapəl nilɣəqin to təkivəŋ əno ənno luqin"
    discourseSegments := []
    glossedTokens := [("təkivəŋ", "ivək.1SG.PRS"), ("əno", "that"), ("əɲɲin", "that"), ("qapəl", "ball"), ("nilɣəqin", "white"), ("to", "and"), ("təkivəŋ", "ivək.1SG.PRS"), ("əno", "that"), ("ənno", "it"), ("luqin", "black")]
    translation := "I allow that the ball is white and I allow that it is black."
    context := "Two balls are in a box: one white, one black. I pull out one and do not show it to you."
    judgment := .acceptable
    alternatives := []
    readings := [("necessity", .unacceptable), ("possibility", .acceptable)]
    paperFeatures := [("section", "2")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex8b : LinguisticExample :=
  { id := "mocnikabramovitz2019_ex8b"
    source := ⟨"mocnik-abramovitz-2019", "(8b)"⟩
    reportedIn := none
    language := "kory1246"
    primaryText := "ujŋe iwke təkitəŋ əno əɲɲin qapəl nilɣəqin to ujŋe iwke təkitəŋ əno ənno luqin"
    discourseSegments := []
    glossedTokens := [("ujŋe", "NEG"), ("iwke", "ivək"), ("təkitəŋ", "AUX.1SG.PRS"), ("əno", "that"), ("əɲɲin", "that"), ("qapəl", "ball"), ("nilɣəqin", "white"), ("to", "and"), ("ujŋe", "NEG"), ("iwke", "ivək"), ("təkitəŋ", "AUX.1SG.PRS"), ("əno", "that"), ("ənno", "it"), ("luqin", "black")]
    translation := "I don't think that the ball is white and I don't think that it is black."
    context := "Two balls are in a box: one white, one black. I pull out one and do not show it to you."
    judgment := .acceptable
    alternatives := []
    readings := [("the thought of (8a)", .acceptable), ("the ball is half white and half black", .unacceptable)]
    paperFeatures := [("section", "2")]
    comment := "iwke is the non-future negated form of ivək (fn. 9)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex9a : LinguisticExample :=
  { id := "mocnikabramovitz2019_ex9a"
    source := ⟨"mocnik-abramovitz-2019", "(9a)"⟩
    reportedIn := none
    language := "kory1246"
    primaryText := "ɣəmmo təkivəŋ, amu jemuqejuʔəŋ"
    discourseSegments := []
    glossedTokens := [("ɣəmmo", "I"), ("təkivəŋ", "ivək.1SG.PRS"), ("amu", "might"), ("jemuqejuʔəŋ", "begin.to.rain.3SG.FUT")]
    translation := "I allow for the possibility that it will rain."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "2")]
    comment := "Translated into Koryak. The adverb amu 'might' facilitates the weaker reading."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex14a : LinguisticExample :=
  { id := "mocnikabramovitz2019_ex14a"
    source := ⟨"mocnik-abramovitz-2019", "(14a)"⟩
    reportedIn := none
    language := "kory1246"
    primaryText := "inenɣəjulevəčʔən ivi əno əninew jejɣučewŋəlʔu metʔaŋ kojajɣočawŋəlaŋ ʔam činin ivi əno əčču qekwaŋ kojajɣočawŋəlaŋ."
    discourseSegments := []
    glossedTokens := [("inenɣəjulevəčʔən", "teacher"), ("ivi", "ivək.3SG.PST"), ("əno", "that"), ("əninew", "his"), ("jejɣučewŋəlʔu", "students"), ("metʔaŋ", "well"), ("kojajɣočawŋəlaŋ", "study.3PL.PRS"), ("ʔam", "but"), ("činin", "self"), ("ivi", "ivək.3SG.PST"), ("əno", "that"), ("əčču", "they"), ("qekwaŋ", "badly"), ("kojajɣočawŋəlaŋ", "study.3PL.PRS")]
    translation := "The teacher said that his students studied well but thought to himself that they studied badly."
    context := "A teacher is always complaining to his wife about how bad his students are. One day, the principal asks him about his students, and he tells him that they are great."
    judgment := .acceptable
    alternatives := [("inenɣəjulevəčʔən ivi əno əninew jejɣučewŋəlʔu metʔaŋ kojajɣočawŋəlaŋ ʔam ivi əno əčču qekwaŋ kojajɣočawŋəlaŋ.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "3")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex14b : LinguisticExample :=
  { id := "mocnikabramovitz2019_ex14b"
    source := ⟨"mocnik-abramovitz-2019", "(14b)"⟩
    reportedIn := none
    language := "kory1246"
    primaryText := "inenɣəjulevəčʔən ivi əno əninew jejɣučewŋəlʔu qekwaŋ kojajɣočawŋəlaŋ ʔam ʔojaŋ ivi əno əčču metʔaŋ kojajɣočawŋəlaŋ"
    discourseSegments := []
    glossedTokens := [("inenɣəjulevəčʔən", "teacher"), ("ivi", "ivək.3SG.PST"), ("əno", "that"), ("əninew", "his"), ("jejɣučewŋəlʔu", "students"), ("qekwaŋ", "badly"), ("kojajɣočawŋəlaŋ", "study.3PL.PRS"), ("ʔam", "but"), ("ʔojaŋ", "openly"), ("ivi", "ivək.3SG.PST"), ("əno", "that"), ("əčču", "they"), ("metʔaŋ", "well"), ("kojajɣočawŋəlaŋ", "study.3PL.PRS")]
    translation := "The teacher thought that his students studied badly but openly said that they studied well."
    context := "A teacher is always complaining to his wife about how bad his students are. One day, the principal asks him about his students, and he tells him that they are great."
    judgment := .acceptable
    alternatives := [("inenɣəjulevəčʔən ivi əno əninew jejɣučewŋəlʔu qekwaŋ kojajɣočawŋəlaŋ ʔam ivi əno əčču metʔaŋ kojajɣočawŋəlaŋ", .unacceptable)]
    readings := []
    paperFeatures := [("section", "3")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex20 : LinguisticExample :=
  { id := "mocnikabramovitz2019_ex20"
    source := ⟨"mocnik-abramovitz-2019", "(20)"⟩
    reportedIn := none
    language := "kory1246"
    primaryText := "inenɣəjulevət͡ɕʔən ivi əno əninew jejɣut͡ɕewŋəlʔu metʔaŋ kojajɣot͡ɕawŋəlaŋ ʔam əno qekwaŋ kojajɣot͡ɕawŋəlaŋ"
    discourseSegments := []
    glossedTokens := [("inenɣəjulevət͡ɕʔən", "teacher"), ("ivi", "ivək.3SG.PST"), ("əno", "that"), ("əninew", "his"), ("jejɣut͡ɕewŋəlʔu", "students"), ("metʔaŋ", "well"), ("kojajɣot͡ɕawŋəlaŋ", "study.3PL.PRS"), ("ʔam", "but"), ("əno", "that"), ("qekwaŋ", "badly"), ("kojajɣot͡ɕawŋəlaŋ", "study.3PL.PRS")]
    translation := "The teacher said that his students are studying well but thought that they were studying badly."
    context := "A principal enters the classroom of a teacher whose students are doing poorly in class and asks him how the students are doing. The teacher doesn't want to disappoint the principal, so he says 'The students are doing well'."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4")]
    comment := "Intended translation; a preliminary result. The source prints t͡ɕ here where (14) prints č for the same affricate."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex2, ex4, ex5, ex6, ex7, ex8a, ex8b, ex9a, ex14a, ex14b, ex20]

end MocnikAbramovitz2019.Examples
