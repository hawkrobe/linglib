module

public import Linglib.Data.Examples.Schema

/-!
# `Oswalt1986` — typed example data

Auto-generated from `Linglib/Data/Examples/Oswalt1986.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Oswalt1986.Examples`.
-/

@[expose] public section

namespace Oswalt1986.Examples

open Data.Examples

def s1 : LinguisticExample :=
  { id := "oswalt1986_s1"
    source := ⟨"oswalt-1986", "(S1)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "qowá·qala"
    discourseSegments := []
    glossedTokens := []
    translation := "I am packing (a suitcase)"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("aspect", "imperfective"), ("evidential", "performative")]
    comment := "The root is indifferent to aspect, so the performative imperfective -ŵela carries the aspect."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s2 : LinguisticExample :=
  { id := "oswalt1986_s2"
    source := ⟨"oswalt-1986", "(S2)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "qowáhmela"
    discourseSegments := []
    glossedTokens := []
    translation := "I just packed"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("aspect", "perfective"), ("evidential", "performative")]
    comment := "The same root with the performative perfective -mela."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s4 : LinguisticExample :=
  { id := "oswalt1986_s4"
    source := ⟨"oswalt-1986", "(S4)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "cohtócʰmela"
    discourseSegments := []
    glossedTokens := []
    translation := "I am leaving"
    context := "Said in the situation in which an English speaker says good-bye."
    judgment := .acceptable
    alternatives := [("cohtocéla", .ungrammatical)]
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("aspect", "perfective"), ("evidential", "performative")]
    comment := "A perfective statement made during the act; cohtoc- is innately perfective, so the imperfective -ŵela cannot be suffixed to it, only to the durative stem of S5."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s6 : LinguisticExample :=
  { id := "oswalt1986_s6"
    source := ⟨"oswalt-1986", "(S6)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "mi·-li ʔa me-ʔe-l pʰak̓úm-mela"
    discourseSegments := []
    glossedTokens := [("mi·-li", "there-VISIBLE"), ("ʔa", "I"), ("me-ʔe-l", "your-father-OBJ"), ("pʰak̓úm-mela", "kill-PERFORM")]
    translation := "Right there I killed your father"
    context := "The sight of the children of a man the speaker killed years earlier prompts the remark."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("aspect", "perfective"), ("evidential", "performative")]
    comment := "Kashaya Texts 7:7.4; the act itself need not have just happened."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s7 : LinguisticExample :=
  { id := "oswalt1986_s7"
    source := ⟨"oswalt-1986", "(S7)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "hú·ʔ men s̓í-ya-m ṭa ʔa"
    discourseSegments := []
    glossedTokens := [("hú·ʔ", "yes"), ("men", "thus"), ("s̓í-ya-m", "do-VISUAL-RESP"), ("ṭa", ""), ("ʔa", "I")]
    translation := "Yes, I have done that"
    context := "A response to a remark by someone else."
    judgment := .acceptable
    alternatives := [("men s̓ímela", .acceptable), ("men s̓ímelam", .ungrammatical)]
    readings := []
    paperFeatures := [("mode", "responsive"), ("aspect", "perfective"), ("evidential", "factualVisual")]
    comment := "The visual takes over for the performative in the responsive mode: the isolated remark men s̓ímela is normal, but the performative with the responsive suffix does not occur. Oswalt leaves the particle ṭa unglossed and marks the rising intonation of the response at the end of the sentence."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s8 : LinguisticExample :=
  { id := "oswalt1986_s8"
    source := ⟨"oswalt-1986", "(S8)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "qowá·qʰ"
    discourseSegments := []
    glossedTokens := []
    translation := "(I see) he is packing"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("aspect", "imperfective"), ("evidential", "factualVisual")]
    comment := "No surface segment is the factual: its presence shows in the length of the final vowel and the aspiration of the stem-final consonant."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s9 : LinguisticExample :=
  { id := "oswalt1986_s9"
    source := ⟨"oswalt-1986", "(S9)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "qowahy"
    discourseSegments := []
    glossedTokens := []
    translation := "(I just saw) he packed, I just saw him pack"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("aspect", "perfective"), ("evidential", "factualVisual")]
    comment := "The same root with the visual perfective -yă."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s13 : LinguisticExample :=
  { id := "oswalt1986_s13"
    source := ⟨"oswalt-1986", "(S13)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "s̓ihta=yacʰma cahno-w"
    discourseSegments := []
    glossedTokens := [("s̓ihta=yacʰma", "bird=PL.SUBJ"), ("cahno-w", "sound-FACTUAL")]
    translation := "Birds sing"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("general truth", .acceptable), ("witnessed", .acceptable)]
    paperFeatures := [("mode", "spontaneous"), ("aspect", "imperfective"), ("evidential", "factualVisual")]
    comment := "The general-truth use of the factual beside the witnessed reading '(I see/saw) birds are/were singing'; with a vowel-final stem the form is also the absolutive, so the sentence can further be read as an evidence-less past."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s14 : LinguisticExample :=
  { id := "oswalt1986_s14"
    source := ⟨"oswalt-1986", "(S14)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "mo·dun"
    discourseSegments := []
    glossedTokens := []
    translation := "I hear/heard someone running along"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("aspect", "imperfective"), ("evidential", "auditory")]
    comment := "The auditory is indifferent to aspect; the stem is imperfective."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s15 : LinguisticExample :=
  { id := "oswalt1986_s15"
    source := ⟨"oswalt-1986", "(S15)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "momá·cin"
    discourseSegments := []
    glossedTokens := []
    translation := "I just heard someone run in"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("aspect", "perfective"), ("evidential", "auditory")]
    comment := "The auditory on the perfective stem of S11."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s16 : LinguisticExample :=
  { id := "oswalt1986_s16"
    source := ⟨"oswalt-1986", "(S16)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "hayu cáhno-n"
    discourseSegments := []
    glossedTokens := []
    translation := "I hear a dog barking"
    context := "Opens a conversation, prompted by the barking."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("evidential", "auditory")]
    comment := "Kashaya Texts 76:6.1, a spontaneous remark recorded in a natural conversation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s17 : LinguisticExample :=
  { id := "oswalt1986_s17"
    source := ⟨"oswalt-1986", "(S17)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "mu hayu cáhno-nna-m"
    discourseSegments := []
    glossedTokens := []
    translation := "[That's why] we hear the dog(s) barking"
    context := "A continuation of the conversation S16 opens."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "responsive"), ("evidential", "auditory")]
    comment := "Kashaya Texts 76:6.4; the response carries the suffix -m and ends in the rising intonation of the response."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s19 : LinguisticExample :=
  { id := "oswalt1986_s19"
    source := ⟨"oswalt-1986", "(S19)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "mu cohtocʰqʰ"
    discourseSegments := []
    glossedTokens := []
    translation := "He must have left, he has left"
    context := "Said on discovering that the person is no longer present; the leaving itself was neither seen nor heard."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("evidential", "inferential")]
    comment := "Inferential I implies no lack of certainty, only the lack of higher-ranking evidence."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s19_visual : LinguisticExample :=
  { id := "oswalt1986_s19_visual"
    source := ⟨"oswalt-1986", "(S19)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "cohtó·y"
    discourseSegments := []
    glossedTokens := []
    translation := "(I just saw) he left"
    context := "The leaving was seen."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("aspect", "perfective"), ("evidential", "factualVisual")]
    comment := "The visual counterpart Oswalt gives for S19."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s19_auditory : LinguisticExample :=
  { id := "oswalt1986_s19_auditory"
    source := ⟨"oswalt-1986", "(S19)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "cohtocin"
    discourseSegments := []
    glossedTokens := []
    translation := "(I heard) he left"
    context := "The leaving was heard."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("aspect", "perfective"), ("evidential", "auditory")]
    comment := "The auditory counterpart Oswalt gives for S19."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s22 : LinguisticExample :=
  { id := "oswalt1986_s22"
    source := ⟨"oswalt-1986", "(S22)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "kalikakʰ dima· s̓i-qa-c̓-qʰ"
    discourseSegments := []
    glossedTokens := [("kalikakʰ", "book"), ("dima·", "holding"), ("s̓i-qa-c̓-qʰ", "make-cause-self-INFER")]
    translation := "He has had a picture taken of himself holding a book"
    context := "The picture is seen; the act of taking it was not."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("evidential", "inferential")]
    comment := "Inferential I where English would not use 'must have'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s25 : LinguisticExample :=
  { id := "oswalt1986_s25"
    source := ⟨"oswalt-1986", "(S25)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "mul =í-yow-e· hayu cáhno-w"
    discourseSegments := []
    glossedTokens := [("mul", "then"), ("=í-yow-e·", "=ASS-P.E.-NONFINAL"), ("hayu", "dog"), ("cáhno-w", "sound-ABS")]
    translation := "Then (I saw, heard, judged) the dog barked"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "narrative"), ("evidential", "personalExperience")]
    comment := "The narrative construction: the personal experience suffix on the assertive enclitic after the first word, the main verb in the absolutive."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s26 : LinguisticExample :=
  { id := "oswalt1986_s26"
    source := ⟨"oswalt-1986", "(S26)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "men s̓i-yíʔciʔ-tʰi-miy"
    discourseSegments := []
    glossedTokens := [("men", "thus"), ("s̓i-yíʔciʔ-tʰi-miy", "do-PL.HABITUAL-NEG-REMOTE")]
    translation := "They never used to do that in the old days"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "remote"), ("evidential", "remotePast")]
    comment := "The archaic remote past, on the main verb rather than displaced in the narrative construction."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s27 : LinguisticExample :=
  { id := "oswalt1986_s27"
    source := ⟨"oswalt-1986", "(S27)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "mul =í-do-· hayu cáhno-w"
    discourseSegments := []
    glossedTokens := [("mul", "then"), ("=í-do-·", "=ASS-QUOT-NONFINAL"), ("hayu", "dog"), ("cáhno-w", "sound-ABS")]
    translation := "Then, they say, the dog barked"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "narrative"), ("evidential", "quotative")]
    comment := "The quotative in the narrative construction, its most common use."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s28 : LinguisticExample :=
  { id := "oswalt1986_s28"
    source := ⟨"oswalt-1986", "(S28)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "meʔ mu mi· sikúhtimeʔ=yacʰma ʔi-do-m ʔul"
    discourseSegments := []
    glossedTokens := [("meʔ", "but"), ("mu", "that"), ("mi·", "there"), ("sikúhtimeʔ=yacʰma", "drinking=people"), ("ʔi-do-m", "be-QUOT-RESP"), ("ʔul", "already")]
    translation := "But I was told the ones that drink are already there"
    context := "From a conversation in the responsive mode; the event takes place elsewhere."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "responsive"), ("evidential", "quotative")]
    comment := "Kashaya Texts 76:19, a rare quotative referring to the present; the sentence ends in the rising intonation of the response."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s29 : LinguisticExample :=
  { id := "oswalt1986_s29"
    source := ⟨"oswalt-1986", "(S29)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "qacúhse hqamac̓-kʰe =ʔ-do-m ṭa"
    discourseSegments := []
    glossedTokens := [("qacúhse", "grass game"), ("hqamac̓-kʰe", "play-FUT"), ("=ʔ-do-m", "=ASS-QUOT-RESP"), ("ṭa", "")]
    translation := "I was told they'll play the grass game"
    context := "From the same conversation as S28."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "responsive"), ("evidential", "quotative")]
    comment := "Kashaya Texts 76:38: the quotative rides on the assertive enclitic into a clause with a future tense. Oswalt leaves the particle ṭa unglossed and marks the rising intonation of the response at the end of the sentence."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def s32 : LinguisticExample :=
  { id := "oswalt1986_s32"
    source := ⟨"oswalt-1986", "(S32)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "kʰe híʔbaya=ʔ-bi-w"
    discourseSegments := []
    glossedTokens := [("kʰe", "my"), ("híʔbaya=ʔ-bi-w", "man=ASS-II-ABS")]
    translation := "It turned out to be my husband"
    context := "A woman saw a man approaching but could not recognize him until he arrived."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("evidential", "inferentialII")]
    comment := "Inferential II with the absolutive, -biw: evidence found after the event makes a partial perception interpretable."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [s1, s2, s4, s6, s7, s8, s9, s13, s14, s15, s16, s17, s19, s19_visual, s19_auditory, s22, s25, s26, s27, s28, s29, s32]

end Oswalt1986.Examples
