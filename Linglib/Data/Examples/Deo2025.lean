import Linglib.Data.Examples.Schema

/-!
# `Deo2025` — typed example data

Auto-generated from `Linglib/Data/Examples/Deo2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Deo2025.Examples`.
-/

namespace Deo2025.Examples

open Data.Examples

def ex_1 : LinguisticExample :=
  { id := "deo2025_1"
    source := ⟨"deo-2025-bara", "(1)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "rəst-e kʰup nisərɖ-e ʣʰa-le ahe-t bərə"
    discourseSegments := []
    glossedTokens := [("rəst-e", "road.M-PL.NOM"), ("kʰup", "very"), ("nisərɖ-e", "slippery-M.PL.NOM"), ("ʣʰa-le", "become-PERF.M.PL"), ("ahe-t", "be.PRES-3.PL"), ("bərə", "BARA")]
    translation := "The roads have become very slippery, (keep this in mind)."
    context := "Anu is going to Mumbai and says to Bilal: I think it will be faster to drive. Bilal: Are you sure? There have been heavy rains..."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "declarative"), ("act", "warning")]
    comment := "Bilal warns Anu to take the road conditions into account before driving."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_2 : LinguisticExample :=
  { id := "deo2025_2"
    source := ⟨"deo-2025-bara", "(2)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "tu mumbəi=la udya ʣa bərə"
    discourseSegments := []
    glossedTokens := [("tu", "you.NOM"), ("mumbəi=la", "Bombay=DAT"), ("udya", "tomorrow"), ("ʣa", "go.IMP"), ("bərə", "BARA")]
    translation := "Go to Mumbai tomorrow, (just do as I say)."
    context := "Same as (1). Bilal: I absolutely don't want you to be driving in this weather..."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "imperative"), ("act", "command")]
    comment := "The particle intensifies the directive force of the imperative."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_3 : LinguisticExample :=
  { id := "deo2025_3"
    source := ⟨"deo-2025-bara", "(3)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "tu maʤʰ-i ʦavi kuʈʰe ʈʰev-li-s bərə"
    discourseSegments := []
    glossedTokens := [("tu", "you.ERG"), ("maʤʰ-i", "my-F.SG.NOM"), ("ʦavi", "key.F.SG.NOM"), ("kuʈʰe", "where"), ("ʈʰev-li-s", "keep-PERF.F.SG-2.SG"), ("bərə", "BARA")]
    translation := "Where did you keep my key? (you better answer right away!)"
    context := "Anu is annoyed because Bilal has hidden her bike key and she needs to get to work urgently. Anu: This is ridiculous..."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "constituent"), ("act", "question")]
    comment := "The wh-interrogative use, which the paper leaves outside its analysis of declaratives and imperatives."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_4 : LinguisticExample :=
  { id := "deo2025_4"
    source := ⟨"deo-2025-bara", "(4)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "mi ata ɔfis=la ʣa-te ahe bərə"
    discourseSegments := []
    glossedTokens := [("mi", "I.NOM"), ("ata", "now"), ("ɔfis=la", "office=DAT"), ("ʣa-te", "go-IMPF.F.SG"), ("ahe", "be.PRES.1.SG"), ("bərə", "BARA")]
    translation := "I am going to the office now (alright?/ok?)."
    context := "Anu needs Bilal to stay at home because the plumber will be coming and someone needs to be in the house to meet him. Anu:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "declarative"), ("act", "informing")]
    comment := "New information relevant to the addressee's actions, with the expectation that he take it on as a commitment; the goal that the plumber be let in is a joint preference."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_5a : LinguisticExample :=
  { id := "deo2025_5a"
    source := ⟨"deo-2025-bara", "(5a)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "aʣ kʰup paus pəɖ-to ahe bərə"
    discourseSegments := []
    glossedTokens := [("aʣ", "today"), ("kʰup", "much"), ("paus", "rain.M.SG.NOM"), ("pəɖ-to", "fall-IMPF.M.SG"), ("ahe", "be.PRES.3.SG"), ("bərə", "BARA")]
    translation := "It is raining hard today (bear in mind)."
    context := "Anu is planning to go to Mumbai today by car. It is raining heavily along the route, impacting road conditions, but the weather will significantly improve tomorrow, making the drive much safer. Bilal says:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "declarative"), ("act", "warning")]
    comment := "Bilal wants Anu to alter her plan and not travel today, offering no alternative plan: her commitment to the content is a precondition for staying safe."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_5b : LinguisticExample :=
  { id := "deo2025_5b"
    source := ⟨"deo-2025-bara", "(5b)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "udya ʦaŋgl-ə unʰ pəɖ-el bərə"
    discourseSegments := []
    glossedTokens := [("udya", "tomorrow"), ("ʦaŋgl-ə", "good-N.SG.NOM"), ("unʰ", "sunshine-N.SG.NOM"), ("pəɖ-el", "fall-FUT.3.SG"), ("bərə", "BARA")]
    translation := "Tomorrow, it will be quite sunny (#bear in mind)."
    context := "Anu is planning to go to Mumbai today by car. It is raining heavily along the route, impacting road conditions, but the weather will significantly improve tomorrow, making the drive much safer. Bilal says:"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "declarative"), ("act", "warning"), ("infelicity", "precondition")]
    comment := "The content points towards one alternative plan among many, so committing to it is not a precondition for the goal. All three consulted speakers rule it out, fn. 3."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_6 : LinguisticExample :=
  { id := "deo2025_6"
    source := ⟨"deo-2025-bara", "(6)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "he əuʃədʰ tum-ʦ-a tap kəmi kər-el bərə"
    discourseSegments := []
    glossedTokens := [("he", "this.N.SG.NOM"), ("əuʃədʰ", "medicine.N.SG.NOM"), ("tum-ʦ-a", "you-GEN-M.SG.NOM"), ("tap", "fever.M.SG.NOM"), ("kəmi", "less"), ("kər-el", "do-FUT.3.SG"), ("bərə", "BARA")]
    translation := "This medicine will lower your fever, (alright?/ok?)."
    context := "Anu has been sick and goes to the doctor, who diagnoses a viral infection. Doctor: Don't worry, the infection will run its course. Meanwhile..."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "declarative"), ("act", "advice")]
    comment := "The doctor's expertise gives the authority to express a preference for dependent commitment; the addressee has no action choices aligned with the goal yet."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_7ctx1 : LinguisticExample :=
  { id := "deo2025_7ctx1"
    source := ⟨"deo-2025-bara", "(7), context 1"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "niʃa tiʧ-ya bəhiɳi=la aɳ-te ahe bərə"
    discourseSegments := []
    glossedTokens := [("niʃa", "Niśa.NOM"), ("tiʧ-ya", "her.GEN-OBL"), ("bəhiɳi=la", "sister.OBL=ACC"), ("aɳ-te", "bring-IMPF.F.SG"), ("ahe", "PRES.3.SG"), ("bərə", "BARA")]
    translation := "Niśa is bringing her sister with her."
    context := "Anu and Bilal are hosting three friends for dinner and they both have been told that one of them will also bring her sister along. Bilal is setting the table. Bilal: Let's see, how many place settings do we need?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "declarative"), ("act", "reminder"), ("infelicity", "alignment")]
    comment := "Anu may reasonably assume that Bilal is aware of the content, so nothing shows his action choices misaligned with it."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_7ctx2 : LinguisticExample :=
  { id := "deo2025_7ctx2"
    source := ⟨"deo-2025-bara", "(7), context 2"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "niʃa tiʧ-ya bəhiɳi=la aɳ-te ahe bərə"
    discourseSegments := []
    glossedTokens := [("niʃa", "Niśa.NOM"), ("tiʧ-ya", "her.GEN-OBL"), ("bəhiɳi=la", "sister.OBL=ACC"), ("aɳ-te", "bring-IMPF.F.SG"), ("ahe", "PRES.3.SG"), ("bərə", "BARA")]
    translation := "Niśa is bringing her sister with her."
    context := "Anu and Bilal are hosting three friends for dinner and they both have been told that one of them will also bring her sister along. It's almost time for the guests and Bilal has laid the table with settings for only five people. Anu: We need six place settings..."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "declarative"), ("act", "reminder")]
    comment := "The table setting is evidence that Bilal's action choices do not reflect commitment to the content."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_8 : LinguisticExample :=
  { id := "deo2025_8"
    source := ⟨"deo-2025-bara", "(8)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "tu=la dəmya-ʦa tras ahe bərə"
    discourseSegments := []
    glossedTokens := [("tu=la", "you.OBL=DAT"), ("dəmya-ʦa", "asthma.OBL-GEN.M.SG.NOM"), ("tras", "suffering.M.SG.NOM"), ("ahe", "be.PRES.3.SG"), ("bərə", "BARA")]
    translation := "You suffer from asthma, (don't forget)."
    context := "Anu has been offered a new job assignment, which requires her to move to a hilly, high-altitude location with steep roads for a year. She is excited about it and is considering it seriously. Bilal prefers that she not make the move for health reasons. Bilal: This could be really difficult for you health-wise..."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "declarative"), ("act", "warning")]
    comment := "Shared content uttered to warn of adverse consequences if it is left out of the decision: a warning and a reminder at once."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_9 : LinguisticExample :=
  { id := "deo2025_9"
    source := ⟨"deo-2025-bara", "(9)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "ho mi ti=la gʰe-un ye-te bərə"
    discourseSegments := []
    glossedTokens := [("ho", "yes"), ("mi", "I.NOM"), ("ti=la", "her.OBL=ACC"), ("gʰe-un", "bring-GER"), ("ye-te", "come-IMPF.F.SG"), ("bərə", "BARA")]
    translation := "Sure, I'll pick her up!"
    context := "Anu and Bilal take turns picking up their daughter Deepa from after-school. It is Bilal's turn today. Bilal tells Anu that he is really busy that day and asks if Anu can pick Deepa up instead. Anu: I understand..."
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "declarative"), ("act", "commissive"), ("infelicity", "source")]
    comment := "A declarative used commissively aligns with a manifest addressee preference: Bilal, who asked, is already a source for the content."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_10a : LinguisticExample :=
  { id := "deo2025_10a"
    source := ⟨"deo-2025-bara", "(10a)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "krupəya tumʰi mə=la həʣar rupye dy-a bərə"
    discourseSegments := []
    glossedTokens := [("krupəya", "please"), ("tumʰi", "you.PL.HON"), ("mə=la", "I.OBL=DAT"), ("həʣar", "thousand"), ("rupye", "rupees"), ("dy-a", "give.IMP-PL"), ("bərə", "BARA")]
    translation := "Please (sir), give me a thousand rupees."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "imperative"), ("act", "request"), ("infelicity", "benefit")]
    comment := "A request: realizing the content benefits the speaker and does not interfere with the addressee's existing preferences."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_10b : LinguisticExample :=
  { id := "deo2025_10b"
    source := ⟨"deo-2025-bara", "(10b)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "koɳi=tari mə=la vihir=it=un baher kaɖʰ-a bərə"
    discourseSegments := []
    glossedTokens := [("koɳi=tari", "someone=PRT"), ("mə=la", "I.OBL=ACC"), ("vihir=it=un", "well.OBL=IN=FROM"), ("baher", "out"), ("kaɖʰ-a", "bring.IMP-PL"), ("bərə", "BARA")]
    translation := "Someone (please) help me come out from this well!"
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "imperative"), ("act", "plea"), ("infelicity", "benefit")]
    comment := "A plea: realizing the content benefits the speaker and is presumed inconsistent with the addressee's existing preferences."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_11a : LinguisticExample :=
  { id := "deo2025_11a"
    source := ⟨"deo-2025-bara", "(11a)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "tu hi rəbəɖi kʰa bərə"
    discourseSegments := []
    glossedTokens := [("tu", "you.NOM"), ("hi", "this.F.SG.NOM"), ("rəbəɖi", "rabadi.F.SG.NOM"), ("kʰa", "eat.IMP.SG"), ("bərə", "BARA")]
    translation := "Try (lit. eat) this rabadi (milk-based dessert)!"
    context := "Anu has made a dessert and is offering it to Bilal to taste. She says:"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "imperative"), ("act", "offer"), ("infelicity", "deference")]
    comment := "With the particle the utterance is understood as a mock command or a veiled threat rather than an offer, fn. 4."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_11b : LinguisticExample :=
  { id := "deo2025_11b"
    source := ⟨"deo-2025-bara", "(11b)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "ho ʣa aɳi məʤa kər-a bərə"
    discourseSegments := []
    glossedTokens := [("ho", "sure"), ("ʣa", "go.IMP.PL"), ("aɳi", "and"), ("məʤa", "fun"), ("kər-a", "do.IMP-PL"), ("bərə", "BARA")]
    translation := "Sure, go and have fun!"
    context := "Deepa and her friends are planning to go to the park and Deepa comes and asks her mother: Mom, can I go play in the park with my friends?"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "imperative"), ("act", "permission"), ("infelicity", "source")]
    comment := "A permission with a well-wish: Deepa has asked, so she is a source for the content."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_11c : LinguisticExample :=
  { id := "deo2025_11c"
    source := ⟨"deo-2025-bara", "(11c)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "ʈʰik ahe ʣa kʰeɭay-la bərə"
    discourseSegments := []
    glossedTokens := [("ʈʰik ahe", "alright"), ("ʣa", "go.IMP"), ("kʰeɭay-la", "play-INF"), ("bərə", "BARA")]
    translation := "Alright! Go and play (if you aren't going to listen!)"
    context := "Anu has asked Deepa to finish her homework before going out to play. Deepa is badgering Anu because she wants to go play without finishing her homework. Anu gets exasperated and says:"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "imperative"), ("act", "concession"), ("infelicity", "source")]
    comment := "A concession: Deepa has revealed her preference for the content and is a source for it."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex_11d : LinguisticExample :=
  { id := "deo2025_11d"
    source := ⟨"deo-2025-bara", "(11d)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "ʣa kʰəɖɖya=t bərə"
    discourseSegments := []
    glossedTokens := [("ʣa", "go.IMP"), ("kʰəɖɖya=t", "ditch.OBL=LOC"), ("bərə", "BARA")]
    translation := "Go to hell (lit. into a ditch)!"
    context := ""
    judgment := .unacceptable
    alternatives := [("ʣa məsəɳa=t bərə", .unacceptable)]
    readings := []
    paperFeatures := [("clauseType", "imperative"), ("act", "curse"), ("infelicity", "benefit")]
    comment := "A curse, detrimental to the addressee; the variant with məsəɳa=t 'burial.ground.OBL=LOC' is the same curse."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_12 : LinguisticExample :=
  { id := "deo2025_12"
    source := ⟨"deo-2025-bara", "(12)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "tu ata ləgeʦ ʣopay-la ʣa bərə"
    discourseSegments := []
    glossedTokens := [("tu", "you.NOM"), ("ata", "now"), ("ləgeʦ", "immediately"), ("ʣopay-la", "sleep-INF"), ("ʣa", "go.IMP"), ("bərə", "BARA")]
    translation := "Get into bed immediately now! (just do as I say)"
    context := "Deepa has stayed up way past her bedtime playing a video game. Anu gets annoyed because Deepa has school tomorrow and needs to be up early. She has already told Deepa several times to go to bed. Anu: You are stretching my patience now..."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "imperative"), ("act", "command")]
    comment := "Anu's authority is made salient; Deepa does not share the goal that she be rested, and her action choices are not aligned with it, fn. 12."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_13 : LinguisticExample :=
  { id := "deo2025_13"
    source := ⟨"deo-2025-bara", "(13)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "kəɖʰəi=mədʰye ətta=ʦ tel ʈaku nəko bərə"
    discourseSegments := []
    glossedTokens := [("kəɖʰəi=mədʰye", "pan.OBL=in"), ("ətta=ʦ", "now=EMPH"), ("tel", "oil.N.SG.NOM"), ("ʈaku", "pour.INF"), ("nəko", "NEG.IMP"), ("bərə", "BARA")]
    translation := "Don't pour the oil into the pan just yet! (or it will go up in flames)"
    context := "Deepa is making dal for the first time with Anu's help and has let the pan get too hot on the stove. She is about to put in some oil to start sautéing the onions. Anu:"
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "imperative"), ("act", "warning")]
    comment := "Deepa is expected to comply in order to ensure her own safety, a goal she most likely shares, fn. 12."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_14 : LinguisticExample :=
  { id := "deo2025_14"
    source := ⟨"deo-2025-bara", "(14)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "ata aʤi=la ek pətrə lihi bərə"
    discourseSegments := []
    glossedTokens := [("ata", "now"), ("aʤi=la", "grandma.OBL=DAT"), ("ek", "one.NOM"), ("pətrə", "note.N.SG.NOM"), ("lihi", "write.IMP"), ("bərə", "BARA")]
    translation := "(Come) now, write a letter to grandma!"
    context := "Deepa got a lovely doll in the mail from Anu's mother and has been playing with it. Anu wants Deepa to thank her grandma before she forgets. Anu: Alright, you have played enough now..."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "imperative"), ("act", "recommendation")]
    comment := "A strong recommendation towards a goal, learning to express gratitude, that the addressee does not share, fn. 12."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_15ctx1 : LinguisticExample :=
  { id := "deo2025_15ctx1"
    source := ⟨"deo-2025-bara", "(15), context 1"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "məg aʣ tu gaɖi gʰe-un ʣa bərə"
    discourseSegments := []
    glossedTokens := [("məg", "then"), ("aʣ", "today"), ("tu", "you.NOM"), ("gaɖi", "car.F.SG.NOM"), ("gʰe-un", "take-GER"), ("ʣa", "go.IMP"), ("bərə", "BARA")]
    translation := "Then, (go ahead and) take the car today."
    context := "Bilal needs to be at a work meeting soon and he has missed the bus that he takes to work. Anu is the one who usually takes the car to work but Bilal would love to be able to drive to work today. Bilal tells Anu he missed the bus. Anu: Ok, so we need to figure out a solution..."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "imperative"), ("act", "recommendation")]
    comment := "Bilal's preference for taking the car is latent, so Anu's proposal sounds like a solicitous command that he will comply with; it cannot be conditionalized with 'if you like', fn. 7."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_15ctx2 : LinguisticExample :=
  { id := "deo2025_15ctx2"
    source := ⟨"deo-2025-bara", "(15), context 2"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "məg aʣ tu gaɖi gʰe-un ʣa bərə"
    discourseSegments := []
    glossedTokens := [("məg", "then"), ("aʣ", "today"), ("tu", "you.NOM"), ("gaɖi", "car.F.SG.NOM"), ("gʰe-un", "take-GER"), ("ʣa", "go.IMP"), ("bərə", "BARA")]
    translation := "Then, (go ahead and) take the car today."
    context := "Bilal needs to be at a work meeting soon and he has missed the bus that he takes to work. Anu is the one who usually takes the car to work but Bilal would love to be able to drive to work today. Bilal tells Anu he missed the bus and adds: I would really like to drive to work today so I don't miss my meeting. Anu:"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "imperative"), ("act", "recommendation"), ("infelicity", "source")]
    comment := "Bilal has revealed his preference, so he is a source for the content."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_16 : LinguisticExample :=
  { id := "deo2025_16"
    source := ⟨"deo-2025-bara", "(16)"⟩
    reportedIn := none
    language := "mara1378"
    primaryText := "ʧʰan tu ti=la gʰe-un ye bərə"
    discourseSegments := []
    glossedTokens := [("ʧʰan", "great"), ("tu", "you.NOM"), ("ti=la", "her.OBL=ACC"), ("gʰe-un", "bring-GER"), ("ye", "come.IMP"), ("bərə", "BARA")]
    translation := "Great, you pick her up and get her (home)!"
    context := "Anu and Bilal take turns picking up their daughter Deepa from after-school. It is Bilal's turn today. Bilal tells Anu that he is really busy that day and doesn't know whether he will make it to the school in time. Anu: No worries, I am working from home today. I will pick her up! Bilal:"
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("clauseType", "imperative"), ("act", "agreement"), ("infelicity", "source")]
    comment := "An imperative agreeing with an actional commitment the addressee has undertaken: Anu is a source for the content."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_19a : LinguisticExample :=
  { id := "deo2025_19a"
    source := ⟨"deo-2025-bara", "(19a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Anu: Keep the discussion we had at this meeting confidential. Nina: Ok/Yes."
    discourseSegments := ["Keep the discussion we had at this meeting confidential.", "Ok/Yes."]
    glossedTokens := []
    translation := ""
    context := "Anu and her secretary Nina, after a sensitive meeting with a small subset of Anu's team."
    judgment := .acceptable
    alternatives := [("Ok", .acceptable), ("Yes", .acceptable)]
    readings := []
    paperFeatures := [("construction", "responseParticle")]
    comment := "Ok takes on Anu's preferential commitment as a dependent, yes commits to the preference independently; only ok admits the continuation 'I had been planning to circulate the minutes', fn. 10."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_19b : LinguisticExample :=
  { id := "deo2025_19b"
    source := ⟨"deo-2025-bara", "(19b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Nina: I will circulate the minutes among all the staff by tomorrow. Anu: No, keep the discussion we had at this meeting confidential. Nina: Ok/#Yes."
    discourseSegments := ["I will circulate the minutes among all the staff by tomorrow.", "No, keep the discussion we had at this meeting confidential.", "Ok/#Yes."]
    glossedTokens := []
    translation := ""
    context := "Anu and her secretary Nina, after a sensitive meeting with a small subset of Anu's team."
    judgment := .acceptable
    alternatives := [("Ok", .acceptable), ("Yes", .unacceptable)]
    readings := []
    paperFeatures := [("construction", "responseParticle")]
    comment := "Nina has expressed an intention incompatible with the preference, so she can no longer commit to it independently with yes."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1, ex_2, ex_3, ex_4, ex_5a, ex_5b, ex_6, ex_7ctx1, ex_7ctx2, ex_8, ex_9, ex_10a, ex_10b, ex_11a, ex_11b, ex_11c, ex_11d, ex_12, ex_13, ex_14, ex_15ctx1, ex_15ctx2, ex_16, ex_19a, ex_19b]

end Deo2025.Examples
