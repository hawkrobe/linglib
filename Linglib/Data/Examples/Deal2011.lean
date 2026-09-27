module

public import Linglib.Data.Examples.Schema

/-!
# `Deal2011` — typed example data

Auto-generated from `Linglib/Data/Examples/Deal2011.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Deal2011.Examples`.
-/

@[expose] public section

namespace Deal2011.Examples

open Data.Examples

def ex1 : LinguisticExample :=
  { id := "deal2011_ex1"
    source := ⟨"deal-2011", "(1)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "'inéhne-no'qa 'ee kii lepít cíickan."
    discourseSegments := []
    glossedTokens := [("'inéhne-no'qa", "take-MOD"), ("'ee", "you"), ("kii", "DEM"), ("lepít", "two"), ("cíickan", "blanket")]
    translation := "You can take these two blankets. / You should take these two blankets."
    context := "A friend is preparing for a camping trip. I am taking this person around my camping supplies and suggesting appropriate things. I hand them two blankets and say:"
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .acceptable)]
    paperFeatures := [("modal", "o'qa"), ("environment", "unembedded")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex5 : LinguisticExample :=
  { id := "deal2011_ex5"
    source := ⟨"deal-2011", "(5)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "kíye pe-ckilíi-toq-o'qa kulaawit-'ásx."
    discourseSegments := []
    glossedTokens := [("kíye", "we"), ("pe-ckilíi-toq-o'qa", "S.PL-return-back-MOD"), ("kulaawit-'ásx", "dark-before")]
    translation := "We have to get home before it gets dark."
    context := "Prompt: We have to get home before it gets dark."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "o'qa"), ("environment", "unembedded"), ("force", "necessity")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex6 : LinguisticExample :=
  { id := "deal2011_ex6"
    source := ⟨"deal-2011", "(6)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "c'alawí 'ee ta'c c'ix̂-n'ipéecwi-se-∅ niimiipuutímt, ilx̂níi-ne c'íiqin 'ee 'a-cóokwa-no'qa."
    discourseSegments := []
    glossedTokens := [("c'alawí", "if"), ("'ee", "you"), ("ta'c", "good"), ("c'ix̂-n'ipéecwi-se-∅", "speak-DES-IMPF-PRES"), ("niimiipuutímt", "Nez.Perce.language"), ("ilx̂níi-ne", "many-OBJ"), ("c'íiqin", "word"), ("'ee", "you"), ("'a-cóokwa-no'qa", "3OBJ-know-MOD")]
    translation := "In order to know the language well, you need to know a lot of words."
    context := "Prompt: To speak well, you have to know a lot of words."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "o'qa"), ("environment", "conditional consequent"), ("force", "necessity")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex10 : LinguisticExample :=
  { id := "deal2011_ex10"
    source := ⟨"deal-2011", "(10)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "'i'yéwki hi-pa-c'íix̂-no'qa."
    discourseSegments := []
    glossedTokens := [("'i'yéwki", "slowly"), ("hi-pa-c'íix̂-no'qa", "3SUBJ-S.PL-speak-MOD")]
    translation := "They should speak slowly."
    context := "A discussion of how young people speak quickly, making them hard to understand."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "o'qa"), ("environment", "unembedded"), ("force", "necessity")]
    comment := "Uttered in casual conversation and translated with should."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex46 : LinguisticExample :=
  { id := "deal2011_ex46"
    source := ⟨"deal-2011", "(46)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "tamáalwit-wecet wéet'u 'ee x̂eeleewi-yo'qa 'étke k'omáy'c 'ee wee-s-∅ 'áatim."
    discourseSegments := []
    glossedTokens := [("tamáalwit-wecet", "rule-reason"), ("wéet'u", "not"), ("'ee", "you"), ("x̂eeleewi-yo'qa", "play-MOD"), ("'étke", "because"), ("k'omáy'c", "hurt"), ("'ee", "you"), ("wee-s-∅", "be-P-PRES"), ("'áatim", "arm")]
    translation := "According to the rules, you can't play, because your arm is injured."
    context := "The referee is talking to an injured player."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "o'qa"), ("environment", "negation"), ("force", "possibility")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex47 : LinguisticExample :=
  { id := "deal2011_ex47"
    source := ⟨"deal-2011", "(47)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "wéet'u kíye kíne pa-w'cáa-yo'qa, kíye ciklíi-six-∅."
    discourseSegments := []
    glossedTokens := [("wéet'u", "not"), ("kíye", "we"), ("kíne", "here"), ("pa-w'cáa-yo'qa", "S.PL-stay-MOD"), ("kíye", "we"), ("ciklíi-six-∅", "go.home-IMPF.PL-PRES")]
    translation := "We can't stay here, we are going home."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "o'qa"), ("environment", "negation"), ("force", "possibility")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex48 : LinguisticExample :=
  { id := "deal2011_ex48"
    source := ⟨"deal-2011", "(48)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "Wéet'u máwa hi-pa-'yáax̂-no'qa 'inpeew'etúu-nm."
    discourseSegments := []
    glossedTokens := [("Wéet'u", "not"), ("máwa", "when"), ("hi-pa-'yáax̂-no'qa", "3SUBJ-S.PL-find-MOD"), ("'inpeew'etúu-nm", "police-ERG")]
    translation := "The police would never find me."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .unacceptable)]
    paperFeatures := [("modal", "o'qa"), ("environment", "negation")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex49 : LinguisticExample :=
  { id := "deal2011_ex49"
    source := ⟨"deal-2011", "(49)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "wéet'u 'ee kiy-ó'qa."
    discourseSegments := []
    glossedTokens := [("wéet'u", "not"), ("'ee", "you"), ("kiy-ó'qa", "go-MOD")]
    translation := "You can't go."
    context := "You are explaining to someone who thinks they have to leave that they are not in fact required to do so. It's not necessary for them to leave."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "o'qa"), ("environment", "negation"), ("force", "necessity")]
    comment := "Consultant: the sentence says 'you can't go', a different conversation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex50 : LinguisticExample :=
  { id := "deal2011_ex50"
    source := ⟨"deal-2011", "(50)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "wéet'u 'ee timiipni-yo'qa."
    discourseSegments := []
    glossedTokens := [("wéet'u", "not"), ("'ee", "you"), ("timiipni-yo'qa", "remember-MOD")]
    translation := "You wouldn't remember."
    context := "I tell someone my number and I see that they are trying to remember it. I say, 'You don't have to remember it; here's my card.'"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "o'qa"), ("environment", "negation"), ("force", "necessity")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex51 : LinguisticExample :=
  { id := "deal2011_ex51"
    source := ⟨"deal-2011", "(51)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "hi-wqíi-cix-∅ 'iléx̂ni hipt ke yox̂ hi-pá-ap-o'qa."
    discourseSegments := []
    glossedTokens := [("hi-wqíi-cix-∅", "3SUBJ-throw.away-IMPF.PL-PRES"), ("'iléx̂ni", "a.lot"), ("hipt", "food"), ("ke", "REL"), ("yox̂", "DEM"), ("hi-pá-ap-o'qa", "3SUBJ-S.PL-eat-MOD")]
    translation := "They are throwing away a lot of food that they could eat. / ... that they should eat."
    context := "I am watching people clean out a cooler and throw away various things."
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .acceptable)]
    paperFeatures := [("modal", "o'qa"), ("environment", "existential restriction")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex52 : LinguisticExample :=
  { id := "deal2011_ex52"
    source := ⟨"deal-2011", "(52)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "hi-wqíi-cix-∅ 'óykala hipt ke yox̂ hi-pá-ap-o'qa."
    discourseSegments := []
    glossedTokens := [("hi-wqíi-cix-∅", "3SUBJ-throw.away-IMPF.PL-PRES"), ("'óykala", "all"), ("hipt", "food"), ("ke", "REL"), ("yox̂", "DEM"), ("hi-pá-ap-o'qa", "3SUBJ-S.PL-eat-MOD")]
    translation := "They are throwing away all the food that they could eat."
    context := "I am watching people clean out a cooler and throw away various things."
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .unacceptable)]
    paperFeatures := [("modal", "o'qa"), ("environment", "universal restriction")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex53 : LinguisticExample :=
  { id := "deal2011_ex53"
    source := ⟨"deal-2011", "(53)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "'e-hitéeme-∅ 'óykala-na ke-m 'a-hitáama-no'qa!"
    discourseSegments := []
    glossedTokens := [("'e-hitéeme-∅", "3OBJ-read-IMPV"), ("'óykala-na", "everything-OBJ"), ("ke-m", "REL-2SG"), ("'a-hitáama-no'qa", "3OBJ-read-MOD")]
    translation := "Read everything you can read!"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .unacceptable)]
    paperFeatures := [("modal", "o'qa"), ("environment", "universal restriction")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex54 : LinguisticExample :=
  { id := "deal2011_ex54"
    source := ⟨"deal-2011", "(54)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "ke-m itúu 'iim kiy-ó'qa 'iin wáaqo' kúu-∅-ye."
    discourseSegments := []
    glossedTokens := [("ke-m", "REL-2SG"), ("itúu", "what"), ("'iim", "you"), ("kiy-ó'qa", "do-MOD"), ("'iin", "I"), ("wáaqo'", "already"), ("kúu-∅-ye", "do-P-REM.PST")]
    translation := "Whatever you can do, I already did."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .unacceptable)]
    paperFeatures := [("modal", "o'qa"), ("environment", "universal restriction")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex57 : LinguisticExample :=
  { id := "deal2011_ex57"
    source := ⟨"deal-2011", "(57)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "c'alawí wéeyux̂ 'u-u-s-∅ k'omáy'c, saykiptaw'atóo-nm háamti'c páa-x-no'qa."
    discourseSegments := []
    glossedTokens := [("c'alawí", "if"), ("wéeyux̂", "leg"), ("'u-u-s-∅", "3GEN-be-P-PRES"), ("k'omáy'c", "injured"), ("saykiptaw'atóo-nm", "doctor-ERG"), ("háamti'c", "quickly"), ("páa-x-no'qa", "3/3-see-MOD")]
    translation := "If he has an injured leg, the doctor needs to see him right away."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "o'qa"), ("environment", "conditional consequent"), ("force", "necessity")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex58 : LinguisticExample :=
  { id := "deal2011_ex58"
    source := ⟨"deal-2011", "(58)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "c'alawí saykiptaw'atóo-nm háamti'c páa-x-no'qa, simíinikem-x hi-kiy-ó'qa."
    discourseSegments := []
    glossedTokens := [("c'alawí", "if"), ("saykiptaw'atóo-nm", "doctor-ERG"), ("háamti'c", "quickly"), ("páa-x-no'qa", "3/3-see-MOD"), ("simíinikem-x", "Lewiston-to"), ("hi-kiy-ó'qa", "3SUBJ-go-MOD")]
    translation := "If the doctor can see him in a hurry, then he should head over to Lewiston."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .unacceptable)]
    paperFeatures := [("modal", "o'qa"), ("environment", "conditional antecedent")]
    comment := "The readings concern the modal of the antecedent."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex59 : LinguisticExample :=
  { id := "deal2011_ex59"
    source := ⟨"deal-2011", "(59)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "c'alawí 'aac-o'qa, kaa 'aac-o'."
    discourseSegments := []
    glossedTokens := [("c'alawí", "if"), ("'aac-o'qa", "enter-MOD"), ("kaa", "then"), ("'aac-o'", "enter-PROSP")]
    translation := "If I can go in, I will go in."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("possibility", .acceptable), ("necessity", .unacceptable)]
    paperFeatures := [("modal", "o'qa"), ("environment", "conditional antecedent")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex60 : LinguisticExample :=
  { id := "deal2011_ex60"
    source := ⟨"deal-2011", "(60)"⟩
    reportedIn := none
    language := "nezp1238"
    primaryText := "c'alawi 'a-múu-no'qa saykiptaw'atóo-na, kaa 'e-múu-nu'."
    discourseSegments := []
    glossedTokens := [("c'alawi", "if"), ("'a-múu-no'qa", "3OBJ-call-MOD"), ("saykiptaw'atóo-na", "doctor-OBJ"), ("kaa", "then"), ("'e-múu-nu'", "3OBJ-call-PROSP")]
    translation := "If I have to call the doctor, I will."
    context := "Prompt: If I have to call the doctor, I will."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("modal", "o'qa"), ("environment", "conditional antecedent"), ("force", "necessity")]
    comment := "Consultant: the sentence says that if I could call the doctor, I would."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex1, ex5, ex6, ex10, ex46, ex47, ex48, ex49, ex50, ex51, ex52, ex53, ex54, ex57, ex58, ex59, ex60]

end Deal2011.Examples
