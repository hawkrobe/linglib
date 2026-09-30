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
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("aspect", "imperfective"), ("evidential", "performative")] }

def s2 : LinguisticExample :=
  { id := "oswalt1986_s2"
    source := ⟨"oswalt-1986", "(S2)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "qowáhmela"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("aspect", "perfective"), ("evidential", "performative")] }

def s4 : LinguisticExample :=
  { id := "oswalt1986_s4"
    source := ⟨"oswalt-1986", "(S4)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "cohtócʰmela"
    glossedTokens := []
    context := "Said in the situation in which an English speaker says good-bye."
    judgment := .acceptable
    alternatives := [("cohtocéla", .ungrammatical)]
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("aspect", "perfective"), ("evidential", "performative")] }

def s6 : LinguisticExample :=
  { id := "oswalt1986_s6"
    source := ⟨"oswalt-1986", "(S6)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "mi·-li ʔa me-ʔe-l pʰak̓úm-mela"
    glossedTokens := [("mi·-li", "there-VISIBLE"), ("ʔa", "I"), ("me-ʔe-l", "your-father-OBJ"), ("pʰak̓úm-mela", "kill-PERFORM")]
    context := "The sight of the children of a man the speaker killed years earlier prompts the remark."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("aspect", "perfective"), ("evidential", "performative")] }

def s7 : LinguisticExample :=
  { id := "oswalt1986_s7"
    source := ⟨"oswalt-1986", "(S7)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "hú·ʔ men s̓í-ya-m ṭa ʔa"
    glossedTokens := [("hú·ʔ", "yes"), ("men", "thus"), ("s̓í-ya-m", "do-VISUAL-RESP"), ("ṭa", ""), ("ʔa", "I")]
    context := "A response to a remark by someone else."
    judgment := .acceptable
    alternatives := [("men s̓ímela", .acceptable), ("men s̓ímelam", .ungrammatical)]
    readings := []
    paperFeatures := [("mode", "responsive"), ("aspect", "perfective"), ("evidential", "factualVisual")] }

def s8 : LinguisticExample :=
  { id := "oswalt1986_s8"
    source := ⟨"oswalt-1986", "(S8)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "qowá·qʰ"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("aspect", "imperfective"), ("evidential", "factualVisual")] }

def s9 : LinguisticExample :=
  { id := "oswalt1986_s9"
    source := ⟨"oswalt-1986", "(S9)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "qowahy"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("aspect", "perfective"), ("evidential", "factualVisual")] }

def s13 : LinguisticExample :=
  { id := "oswalt1986_s13"
    source := ⟨"oswalt-1986", "(S13)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "s̓ihta=yacʰma cahno-w"
    glossedTokens := [("s̓ihta=yacʰma", "bird=PL.SUBJ"), ("cahno-w", "sound-FACTUAL")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("general truth", .acceptable), ("witnessed", .acceptable)]
    paperFeatures := [("mode", "spontaneous"), ("aspect", "imperfective"), ("evidential", "factualVisual")] }

def s14 : LinguisticExample :=
  { id := "oswalt1986_s14"
    source := ⟨"oswalt-1986", "(S14)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "mo·dun"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("aspect", "imperfective"), ("evidential", "auditory")] }

def s15 : LinguisticExample :=
  { id := "oswalt1986_s15"
    source := ⟨"oswalt-1986", "(S15)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "momá·cin"
    glossedTokens := []
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("aspect", "perfective"), ("evidential", "auditory")] }

def s16 : LinguisticExample :=
  { id := "oswalt1986_s16"
    source := ⟨"oswalt-1986", "(S16)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "hayu cáhno-n"
    glossedTokens := []
    context := "Opens a conversation, prompted by the barking."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("evidential", "auditory")] }

def s17 : LinguisticExample :=
  { id := "oswalt1986_s17"
    source := ⟨"oswalt-1986", "(S17)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "mu hayu cáhno-nna-m"
    glossedTokens := []
    context := "A continuation of the conversation S16 opens."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "responsive"), ("evidential", "auditory")] }

def s19 : LinguisticExample :=
  { id := "oswalt1986_s19"
    source := ⟨"oswalt-1986", "(S19)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "mu cohtocʰqʰ"
    glossedTokens := []
    context := "Said on discovering that the person is no longer present; the leaving itself was neither seen nor heard."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("evidential", "inferential")] }

def s19_visual : LinguisticExample :=
  { id := "oswalt1986_s19_visual"
    source := ⟨"oswalt-1986", "(S19)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "cohtó·y"
    glossedTokens := []
    context := "The leaving was seen."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("aspect", "perfective"), ("evidential", "factualVisual")] }

def s19_auditory : LinguisticExample :=
  { id := "oswalt1986_s19_auditory"
    source := ⟨"oswalt-1986", "(S19)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "cohtocin"
    glossedTokens := []
    context := "The leaving was heard."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("aspect", "perfective"), ("evidential", "auditory")] }

def s22 : LinguisticExample :=
  { id := "oswalt1986_s22"
    source := ⟨"oswalt-1986", "(S22)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "kalikakʰ dima· s̓i-qa-c̓-qʰ"
    glossedTokens := [("kalikakʰ", "book"), ("dima·", "holding"), ("s̓i-qa-c̓-qʰ", "make-cause-self-INFER")]
    context := "The picture is seen; the act of taking it was not."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "spontaneous"), ("evidential", "inferential")] }

def s25 : LinguisticExample :=
  { id := "oswalt1986_s25"
    source := ⟨"oswalt-1986", "(S25)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "mul =í-yow-e· hayu cáhno-w"
    glossedTokens := [("mul", "then"), ("=í-yow-e·", "=ASS-P.E.-NONFINAL"), ("hayu", "dog"), ("cáhno-w", "sound-ABS")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "narrative"), ("evidential", "personalExperience")] }

def s26 : LinguisticExample :=
  { id := "oswalt1986_s26"
    source := ⟨"oswalt-1986", "(S26)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "men s̓i-yíʔciʔ-tʰi-miy"
    glossedTokens := [("men", "thus"), ("s̓i-yíʔciʔ-tʰi-miy", "do-PL.HABITUAL-NEG-REMOTE")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "remote"), ("evidential", "remotePast")] }

def s27 : LinguisticExample :=
  { id := "oswalt1986_s27"
    source := ⟨"oswalt-1986", "(S27)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "mul =í-do-· hayu cáhno-w"
    glossedTokens := [("mul", "then"), ("=í-do-·", "=ASS-QUOT-NONFINAL"), ("hayu", "dog"), ("cáhno-w", "sound-ABS")]
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "narrative"), ("evidential", "quotative")] }

def s28 : LinguisticExample :=
  { id := "oswalt1986_s28"
    source := ⟨"oswalt-1986", "(S28)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "meʔ mu mi· sikúhtimeʔ=yacʰma ʔi-do-m ʔul"
    glossedTokens := [("meʔ", "but"), ("mu", "that"), ("mi·", "there"), ("sikúhtimeʔ=yacʰma", "drinking=people"), ("ʔi-do-m", "be-QUOT-RESP"), ("ʔul", "already")]
    context := "From a conversation in the responsive mode; the event takes place elsewhere."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "responsive"), ("evidential", "quotative")] }

def s29 : LinguisticExample :=
  { id := "oswalt1986_s29"
    source := ⟨"oswalt-1986", "(S29)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "qacúhse hqamac̓-kʰe =ʔ-do-m ṭa"
    glossedTokens := [("qacúhse", "grass game"), ("hqamac̓-kʰe", "play-FUT"), ("=ʔ-do-m", "=ASS-QUOT-RESP"), ("ṭa", "")]
    context := "From the same conversation as S28."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("mode", "responsive"), ("evidential", "quotative")] }

def s32 : LinguisticExample :=
  { id := "oswalt1986_s32"
    source := ⟨"oswalt-1986", "(S32)"⟩
    reportedIn := none
    language := "kash1280"
    primaryText := "kʰe híʔbaya=ʔ-bi-w"
    glossedTokens := [("kʰe", "my"), ("híʔbaya=ʔ-bi-w", "man=ASS-II-ABS")]
    context := "A woman saw a man approaching but could not recognize him until he arrived."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("evidential", "inferentialII")] }

def all : List LinguisticExample := [s1, s2, s4, s6, s7, s8, s9, s13, s14, s15, s16, s17, s19, s19_visual, s19_auditory, s22, s25, s26, s27, s28, s29, s32]

end Oswalt1986.Examples
