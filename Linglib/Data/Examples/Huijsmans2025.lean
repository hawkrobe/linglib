import Linglib.Data.Examples.Schema

/-!
# `Huijsmans2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Huijsmans2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Huijsmans2025.Examples`.
-/

namespace Huijsmans2025.Examples

open Data.Examples

def ex37 : LinguisticExample :=
  { id := "huijsmans2025_ex37"
    source := ⟨"huijsmans-2025", "(37)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She seems to be very sick."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "P visits M in the hospital and sees through the window that the doctors look worried."
    judgment := .acceptable
    alternatives := [("She should be very sick.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.1"), ("modal", "seems"), ("timing", "evidence acquired after the event")]
    comment := "Reported from Hirayama and Matthewson (2022)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex38 : LinguisticExample :=
  { id := "huijsmans2025_ex38"
    source := ⟨"huijsmans-2025", "(38)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She should be very sick."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "P poisons M's food and leaves."
    judgment := .acceptable
    alternatives := [("She seems to be very sick.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.1"), ("modal", "should"), ("timing", "evidence acquired before the event")]
    comment := "Reported from Hirayama and Matthewson (2022)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex40 : LinguisticExample :=
  { id := "huijsmans2025_ex40"
    source := ⟨"huijsmans-2025", "(40)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "səmkʷi č̓ɛχ."
    discourseSegments := []
    glossedTokens := [("səm=kʷi", "FUT=CL.DEM"), ("č̓əx̌", "get.cooked")]
    translation := "It will be cooked."
    context := "We are outside, but I have a fish cooking in the oven. I check my watch and realize that it should be cooked."
    judgment := .acceptable
    alternatives := [("č̓ɛkʷi č̓ɛχ.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "səm"), ("timing", "MBT < PrejT")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex41 : LinguisticExample :=
  { id := "huijsmans2025_ex41"
    source := ⟨"huijsmans-2025", "(41)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It will be cooked (by now)."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Same as (40)."
    judgment := .acceptable
    alternatives := [("It must be cooked (by now).", .acceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "will"), ("timing", "MBT < PrejT")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex42 : LinguisticExample :=
  { id := "huijsmans2025_ex42"
    source := ⟨"huijsmans-2025", "(42)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "səmkʷi θo hɛwt."
    discourseSegments := []
    glossedTokens := [("səm=kʷi", "FUT=CL.DEM"), ("θu", "go"), ("hiwt", "get.home")]
    translation := "He must have gotten home."
    context := "Daniel left from t̓ɩšosəm to go back home to Vancouver. We know he left pretty early, so in the evening when we see the time, I say:"
    judgment := .acceptable
    alternatives := [("č̓ɛkʷi θo hɛwt.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "səm"), ("timing", "MBT < PrejT")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex43 : LinguisticExample :=
  { id := "huijsmans2025_ex43"
    source := ⟨"huijsmans-2025", "(43)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He will have gotten home (by now)."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Same as (42)."
    judgment := .acceptable
    alternatives := [("He must have gotten home (by now).", .acceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "will"), ("timing", "MBT < PrejT")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex44 : LinguisticExample :=
  { id := "huijsmans2025_ex44"
    source := ⟨"huijsmans-2025", "(44)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "səmkʷi qey."
    discourseSegments := []
    glossedTokens := [("səm=kʷi", "FUT=CL.DEM"), ("qəy", "die")]
    translation := "He'll be dead."
    context := "The villain puts poison in the hero's food that he has prepped for dinner and then leaves. An hour or so after dinnertime, the villain tells his sidekick:"
    judgment := .acceptable
    alternatives := [("č̓ɛkʷi qey.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "səm"), ("timing", "MBT < PrejT")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex45 : LinguisticExample :=
  { id := "huijsmans2025_ex45"
    source := ⟨"huijsmans-2025", "(45)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He will be dead (by now)."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Same as (44)."
    judgment := .acceptable
    alternatives := [("He must be dead (by now).", .acceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "will"), ("timing", "MBT < PrejT")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex46 : LinguisticExample :=
  { id := "huijsmans2025_ex46"
    source := ⟨"huijsmans-2025", "(46)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "χʷɛt səmkʷa ƛəm̓mot Felipe. saymot kʷ č̓ɩɬ ʔi xʷukʷt č̓ɩɬukʷts."
    discourseSegments := []
    glossedTokens := [("xʷit", "really"), ("səm=kʷa", "FUT=CL.DEM"), ("ƛəm̓-mut", "get.wet-INT"), ("Felipe", "Felipe"), ("saymut", "intense"), ("kʷ=čəɬ", "DET=rain"), ("ʔiy", "CONJ"), ("xʷukʷt", "not.exist"), ("čəɬ-ukʷt-s", "rain-jacket-3POSS")]
    translation := "Felipe will have gotten really soaked. It's pouring, and he didn't have a rain jacket."
    context := "Felipe always bikes home at 5. I haven't been paying attention to the weather, but at 6 I look out the window and see that it is pouring and has been for some time. Then I notice that Felipe left his coat in my bag."
    judgment := .acceptable
    alternatives := [("χʷɛt č̓ɛkʷa ƛəm̓mot Felipe.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "səm"), ("timing", "MBT < PrejT but ET < EAT"), ("role", "wedge against the EAT analysis")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex47 : LinguisticExample :=
  { id := "huijsmans2025_ex47"
    source := ⟨"huijsmans-2025", "(47)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Felipe will have gotten really soaked. It's pouring, and he didn't have a rain jacket."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Same as (46)."
    judgment := .acceptable
    alternatives := [("Felipe must have gotten really soaked.", .acceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "will"), ("timing", "MBT < PrejT but ET < EAT"), ("role", "wedge against the EAT analysis")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex48 : LinguisticExample :=
  { id := "huijsmans2025_ex48"
    source := ⟨"huijsmans-2025", "(48)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "hɛhɛw səmkʷa č̓ɩmč̓ɛʔmamot."
    discourseSegments := []
    glossedTokens := [("hihiw", "really"), ("səm=kʷa", "FUT=CL.DEM"), ("č̓əm̓~č̓əm-əm-mut", "cold~CHAR-MD-INT")]
    translation := "She will have been really cold!"
    context := "It's winter. Last night, it was very cold, with strong winds and some snow. Today, I find out that my friend had been clam-digging last night."
    judgment := .acceptable
    alternatives := [("hɛhɛw č̓ɛkʷa č̓ɩmč̓ɛʔmamot.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "səm"), ("timing", "MBT < PrejT but ET < EAT")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex49 : LinguisticExample :=
  { id := "huijsmans2025_ex49"
    source := ⟨"huijsmans-2025", "(49)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "She will have been really cold!"
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Same as (48)."
    judgment := .acceptable
    alternatives := [("She must have been really cold!", .acceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "will"), ("timing", "MBT < PrejT but ET < EAT")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex50 : LinguisticExample :=
  { id := "huijsmans2025_ex50"
    source := ⟨"huijsmans-2025", "(50)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "č̓ɛkʷi č̓ɛχ."
    discourseSegments := []
    glossedTokens := [("č̓a=kʷi", "INFER=CL.DEM"), ("č̓əx̌", "get.cooked")]
    translation := "It must be cooked."
    context := "I'm cooking a fish, and I'm guessing by the smell that it is cooked."
    judgment := .acceptable
    alternatives := [("səmkʷi č̓ɛχ.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "č̓ɛ"), ("timing", "PrejT ≤ MBT")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex51 : LinguisticExample :=
  { id := "huijsmans2025_ex51"
    source := ⟨"huijsmans-2025", "(51)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It must be cooked (by now)."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Same as (50)."
    judgment := .acceptable
    alternatives := [("It will be cooked (by now).", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "must"), ("timing", "PrejT ≤ MBT")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex52 : LinguisticExample :=
  { id := "huijsmans2025_ex52"
    source := ⟨"huijsmans-2025", "(52)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "č̓ɛkʷi θo hɛwt."
    discourseSegments := []
    glossedTokens := [("č̓a=kʷi", "INFER=CL.DEM"), ("θu", "go"), ("hiwt", "get.home")]
    translation := "He must have gotten home."
    context := "Someone was out earlier, and now I see his car in his driveway."
    judgment := .acceptable
    alternatives := [("səmkʷi θo hɛwt.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "č̓ɛ"), ("timing", "PrejT ≤ MBT")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex53 : LinguisticExample :=
  { id := "huijsmans2025_ex53"
    source := ⟨"huijsmans-2025", "(53)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He must have gotten home."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Same as (52)."
    judgment := .acceptable
    alternatives := [("He will have gotten home.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "must"), ("timing", "PrejT ≤ MBT")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex54 : LinguisticExample :=
  { id := "huijsmans2025_ex54"
    source := ⟨"huijsmans-2025", "(54)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "qəqey=č̓ɛ."
    discourseSegments := []
    glossedTokens := [("qəqey=č̓a", "dead=INFER")]
    translation := "It must be dead."
    context := "My brother was hiking, and at one point there was a cliff looking out over the water. Looking down, he could see a bear, but it was just laid out, not moving."
    judgment := .acceptable
    alternatives := [("qəqey=səm.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "č̓ɛ"), ("timing", "PrejT ≤ MBT")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex55 : LinguisticExample :=
  { id := "huijsmans2025_ex55"
    source := ⟨"huijsmans-2025", "(55)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It must be dead."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Same as (54)."
    judgment := .acceptable
    alternatives := [("It will be dead.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "must"), ("timing", "PrejT ≤ MBT")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex56 : LinguisticExample :=
  { id := "huijsmans2025_ex56"
    source := ⟨"huijsmans-2025", "(56)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "qʷol č̓ɛ səmt χəpi. xʷaʔčxʷ χaχƛɛmaxʷ."
    discourseSegments := []
    glossedTokens := [("qʷəl̓=ča=səm=ʔut", "come=INFER=FUT=EXCL"), ("χəpəy", "return"), ("xʷaʔ=čxʷ", "NEG=2SG.SBJ"), ("χaχƛim=axʷ", "worry=2SG.SBJV")]
    translation := "He'll come back. Don't worry."
    context := "Tim is Bailey's cat that's gone missing. Even though she doesn't have any knowledge of what is going on with him, Gloria is trying to reassure Bailey."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "č̓ɛ"), ("timing", "no evidence")]
    comment := "Based on Bhadra (2016): the inferential needs evidence arising at or after the prejacent."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex57 : LinguisticExample :=
  { id := "huijsmans2025_ex57"
    source := ⟨"huijsmans-2025", "(57)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "č̓ɛkʷi nɛʔ ʔamot."
    discourseSegments := []
    glossedTokens := [("č̓a=kʷi", "INFER=CL.DEM"), ("niʔ", "be.there"), ("ʔamut", "be.home")]
    translation := "He must be home."
    context := "It's after 6, the time when my brother would usually be home from work. I drive past his place and see that his car is in the driveway and his lights are on."
    judgment := .acceptable
    alternatives := [("səmkʷi nɛʔ ʔamot.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "č̓ɛ"), ("timing", "evidence before and at PrejT")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex58 : LinguisticExample :=
  { id := "huijsmans2025_ex58"
    source := ⟨"huijsmans-2025", "(58)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He must be home."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Same as (57)."
    judgment := .acceptable
    alternatives := [("He will be home.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "must"), ("timing", "evidence before and at PrejT")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex59 : LinguisticExample :=
  { id := "huijsmans2025_ex59"
    source := ⟨"huijsmans-2025", "(59)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "səmkʷi č̓ɛχ šɛtᶿ kʷukʷ."
    discourseSegments := []
    glossedTokens := [("səm=kʷi", "FUT=CL.DEM"), ("č̓əx̌", "get.cooked"), ("šə=tᶿ=kʷukʷ", "DET=1SG.POSS=cook")]
    translation := "My cooking will be cooked."
    context := "This fish has been in the oven for 20 min, which should be sufficient given its size. In addition, the fish is starting to smell cooked."
    judgment := .acceptable
    alternatives := [("č̓ɛkʷi č̓ɛχ šɛtᶿ kʷukʷ.", .acceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "səm or č̓ɛ"), ("timing", "the smell may be set aside")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex60 : LinguisticExample :=
  { id := "huijsmans2025_ex60"
    source := ⟨"huijsmans-2025", "(60)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The fish will be cooked."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Same as (59)."
    judgment := .acceptable
    alternatives := [("The fish must be cooked.", .acceptable)]
    readings := []
    paperFeatures := [("section", "4.2"), ("modal", "will or must"), ("timing", "the smell may be set aside")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex68 : LinguisticExample :=
  { id := "huijsmans2025_ex68"
    source := ⟨"huijsmans-2025", "(68)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "hoθotoɬ Freddie sqʷols səm ʔəkʷ meeting, ʔi kʷa xʷaʔ qʷol̓əs."
    discourseSegments := []
    glossedTokens := [("huθut-uɬ", "say-PST"), ("Freddie", "Freddie"), ("s=qʷəl=s=səm", "NMLZ=come=3POSS=FUT"), ("ʔə=kʷ=meeting", "OBL=DET=meeting"), ("ʔiy", "CONJ"), ("kʷa=xʷaʔ", "CL.DEM=NEG"), ("qʷəl̓=as", "come=3SBJV")]
    translation := "Freddie said he would come to the meeting, but he never arrived."
    context := "We had a meeting this morning, and Freddie had told me he would come, but never showed up."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5"), ("perspective", "past"), ("orientation", "future"), ("environment", "embedded")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex69 : LinguisticExample :=
  { id := "huijsmans2025_ex69"
    source := ⟨"huijsmans-2025", "(69)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "payɛ ʔot t̓ᶿɛt̓ᶿɛyʔəm ʔəkʷ tam kʷ yɛtɛt ʔi manom səm."
    discourseSegments := []
    glossedTokens := [("payaʔ=ʔut", "always=EXCL"), ("t̓ᶿi~t̓iy-ʔəm", "PROG~search-ACT.INTR"), ("ʔə=kʷ=tam", "OBL=DET=thing"), ("kʷ", "DET"), ("yəʔ-t=it", "do-CTR=3PL.POSS"), ("ʔi", "CONJ"), ("məʔ-nu-m=səm", "get-NCTR-PASS=FUT")]
    translation := "They were always searching for something to do so he would be caught."
    context := "From a traditional story about Mink and Wolf."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5"), ("perspective", "past"), ("orientation", "future"), ("environment", "narrative")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex70 : LinguisticExample :=
  { id := "huijsmans2025_ex70"
    source := ⟨"huijsmans-2025", "(70)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "ƛ̓ič̓t səm maʔnas"
    discourseSegments := []
    glossedTokens := [("ƛ̓<i>č̓t=səm", "fall.asleep<STAT>=FUT"), ("maʔna-s", "child-3POSS")]
    translation := "Her baby will be asleep."
    context := "I know my friend's baby's naptime. I take a look at the clock and decide not to call because the baby will be asleep."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5"), ("orientation", "present")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex71 : LinguisticExample :=
  { id := "huijsmans2025_ex71"
    source := ⟨"huijsmans-2025", "(71)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "ƛ̓ič̓t səm maʔnas"
    discourseSegments := []
    glossedTokens := [("ƛ̓<i>č̓t=səm", "fall.asleep<STAT>=FUT"), ("maʔna-s", "child-3POSS")]
    translation := "Her baby will be asleep."
    context := "Over breakfast on a Saturday Felipe suggests going to drop in on our cousin in the afternoon, but I know the time he's thinking is when her baby will be napping."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5"), ("orientation", "future")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex75 : LinguisticExample :=
  { id := "huijsmans2025_ex75"
    source := ⟨"huijsmans-2025", "(75)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "A man came in at four. He would leave at eight. For the four hours he would be here, he would simply sit quietly in the corner looking out the window."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5"), ("modal", "would"), ("perspective", "past")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex76 : LinguisticExample :=
  { id := "huijsmans2025_ex76"
    source := ⟨"huijsmans-2025", "(76)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Her baby will be asleep."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "I know my friend's baby's naptime. I take a look at the clock and decide not to call because the baby will be asleep."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5"), ("modal", "will"), ("orientation", "present")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex77 : LinguisticExample :=
  { id := "huijsmans2025_ex77"
    source := ⟨"huijsmans-2025", "(77)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Her baby will be asleep."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "Over breakfast on a Saturday Felipe suggests going to drop in on our cousin in the afternoon, but I know the time he's thinking is when her baby will be napping."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5"), ("modal", "will"), ("orientation", "future")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex91 : LinguisticExample :=
  { id := "huijsmans2025_ex91"
    source := ⟨"huijsmans-2025", "(91)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "ʔamot č̓ɛ Freddie. χʷaʔwɩ́t tə nɩkʷayus."
    discourseSegments := []
    glossedTokens := [("ʔamut=č̓a", "be.home=INFER"), ("Freddie", "Freddie"), ("xʷəw̓-ít", "get.lit-STAT"), ("tə=nikʷayu-s", "DET=light-3POSS")]
    translation := "Freddie must be home. His lights are on."
    context := "We go past Freddie's home, and I say that he must be home because his lights are on."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("modal", "č̓ɛ"), ("orientation", "present")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex92 : LinguisticExample :=
  { id := "huijsmans2025_ex92"
    source := ⟨"huijsmans-2025", "(92)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "ʔɛʔɛχaǰɛʔoɬ č̓ɛ Betty. niš kʷikʷʔɛ́t tə k̓ʷimɛns."
    discourseSegments := []
    glossedTokens := [("ʔi~ʔix̌aǰa-uɬ=ča", "PROG~clean.roots-PST=INFER"), ("Betty", "Betty"), ("niš", "be.here"), ("kʷi<kʷ>ʔ-ít", "laid.out<PL>-STAT"), ("tə=k̓ʷimin-s", "DET=waste-3POSS")]
    translation := "Betty must have been cleaning roots. The waste bits are scattered about."
    context := "I go over to Betty's house for dinner, and as I'm approaching her front door, I see fresh shavings of cedar roots scattered on the grass."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("modal", "č̓ɛ"), ("orientation", "past")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex93 : LinguisticExample :=
  { id := "huijsmans2025_ex93"
    source := ⟨"huijsmans-2025", "(93)"⟩
    reportedIn := none
    language := "como1259"
    primaryText := "č̓ɩɬ č̓ɛ səm. ti qʷol nɛʔayɩtanəm."
    discourseSegments := []
    glossedTokens := [("č̓əɬ=ča=səm", "rain=INFER=FUT"), ("ti", "CL.DEM"), ("qʷəl̓", "come"), ("niʔayitanəm", "cloudy")]
    translation := "It must be going to rain. It's clouding over."
    context := "You feel a change in the weather and see storm clouds gathering."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("section", "5.1"), ("modal", "č̓ɛ over səm"), ("timing", "two presuppositions")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex97 : LinguisticExample :=
  { id := "huijsmans2025_ex97"
    source := ⟨"huijsmans-2025", "(97)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Her baby will be asleep."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := "I know my friend's baby's naptime. I take a look at the clock and decide not to call because the baby will be asleep."
    judgment := .acceptable
    alternatives := [("Her baby must be asleep.", .unacceptable)]
    readings := []
    paperFeatures := [("section", "5.1"), ("modal", "will"), ("pragmatics", "Maximize Presupposition")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex37, ex38, ex40, ex41, ex42, ex43, ex44, ex45, ex46, ex47, ex48, ex49, ex50, ex51, ex52, ex53, ex54, ex55, ex56, ex57, ex58, ex59, ex60, ex68, ex69, ex70, ex71, ex75, ex76, ex77, ex91, ex92, ex93, ex97]

end Huijsmans2025.Examples
