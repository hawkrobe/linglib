import Linglib.Data.Examples.Schema

/-!
# `Dixon1994` — typed example data

Auto-generated from `Linglib/Data/Examples/Dixon1994.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Dixon1994.Examples`.
-/

namespace Dixon1994.Examples

open Data.Examples

def ex_1_2_5 : LinguisticExample :=
  { id := "dixon1994_1_2_5"
    source := ⟨"dixon-1994", "§1.2 (5)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma banaga-nyu"
    discourseSegments := []
    glossedTokens := [("ŋuma", "father.ABS"), ("banaga-nyu", "return-NONFUT")]
    translation := "Father returned."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "simple"), ("function", "S")]
    comment := "A noun in S function bears absolutive case, with zero realisation; noun markers are omitted throughout, fn. 8."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_1_2_7 : LinguisticExample :=
  { id := "dixon1994_1_2_7"
    source := ⟨"dixon-1994", "§1.2 (7)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma yabu-ŋgu bura-n"
    discourseSegments := []
    glossedTokens := [("ŋuma", "father.ABS"), ("yabu-ŋgu", "mother-ERG"), ("bura-n", "see-NONFUT")]
    translation := "Mother saw father."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "simple"), ("function", "AO")]
    comment := "A noun in O function is absolutive like S; A takes ergative -ŋgu; the verb cross-references none of S, A and O."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_1_2_12 : LinguisticExample :=
  { id := "dixon1994_1_2_12"
    source := ⟨"dixon-1994", "§1.2 (12)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma bural-ŋa-nyu yabu-gu"
    discourseSegments := []
    glossedTokens := [("ŋuma", "father.ABS"), ("bural-ŋa-nyu", "see-ANTIPASS-NONFUT"), ("yabu-gu", "mother-DAT")]
    translation := "Father saw mother."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "antipassive"), ("function", "S")]
    comment := "The antipassive of §1.2 (8): underlying A becomes S, underlying O goes into dative case, and the verb bears -ŋa-y between root and inflection, (11)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_15 : LinguisticExample :=
  { id := "dixon1994_15"
    source := ⟨"dixon-1994", "§6.2.2 (15)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "nyurra ŋana-na bura-n"
    discourseSegments := []
    glossedTokens := [("nyurra", "you.all.NOM"), ("ŋana-na", "we.all-ACC"), ("bura-n", "see-NONFUT")]
    translation := "You all saw us."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "simple"), ("function", "AO")]
    comment := "First and second person pronouns inflect on a nominative-accusative pattern, Table 6.1: the split of Table 4.1."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_17 : LinguisticExample :=
  { id := "dixon1994_17"
    source := ⟨"dixon-1994", "§6.2.2 (17)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma banaga-nyu miyanda-nyu"
    discourseSegments := []
    glossedTokens := [("ŋuma", "father.ABS"), ("banaga-nyu", "return-NONFUT"), ("miyanda-nyu", "laugh-NONFUT")]
    translation := "Father returned and laughed."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "S"), ("second", "S"), ("derivation", "none")]
    comment := "Possibility (a): the common NP is in pivot function S in both clauses and its second occurrence is omitted; there is no overt coordinator."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_19 : LinguisticExample :=
  { id := "dixon1994_19"
    source := ⟨"dixon-1994", "§6.2.2 (19)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma banaga-nyu yabu-ŋgu bura-n"
    discourseSegments := []
    glossedTokens := [("ŋuma", "father.ABS"), ("banaga-nyu", "return-NONFUT"), ("yabu-ŋgu", "mother-ERG"), ("bura-n", "see-NONFUT")]
    translation := "Father returned and mother saw him."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "S"), ("second", "O"), ("derivation", "none")]
    comment := "Possibility (b), S₁ = O₂: both are pivot functions under the S/O pivot."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_20 : LinguisticExample :=
  { id := "dixon1994_20"
    source := ⟨"dixon-1994", "§6.2.2 (20)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋana banaga-nyu nyurra bura-n"
    discourseSegments := []
    glossedTokens := [("ŋana", "we.all.NOM"), ("banaga-nyu", "return-NONFUT"), ("nyurra", "you.all.NOM"), ("bura-n", "see-NONFUT")]
    translation := "We returned and you all saw us."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "S"), ("second", "O"), ("derivation", "none")]
    comment := "The pivot is S/O for pronouns too, although their morphology is accusative: ŋana is retained and ŋana-na omitted."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_21 : LinguisticExample :=
  { id := "dixon1994_21"
    source := ⟨"dixon-1994", "§6.2.2 (21)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma yabu-ŋgu bura-n banaga-nyu"
    discourseSegments := []
    glossedTokens := [("ŋuma", "father.ABS"), ("yabu-ŋgu", "mother-ERG"), ("bura-n", "see-NONFUT"), ("banaga-nyu", "return-NONFUT")]
    translation := "Mother saw father and he returned."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "O"), ("second", "S"), ("derivation", "none")]
    comment := "Possibility (d), O₁ = S₂."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_24 : LinguisticExample :=
  { id := "dixon1994_24"
    source := ⟨"dixon-1994", "§6.2.2 (24)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma yabu-ŋgu bura-n jaja-ŋgu ŋamba-n"
    discourseSegments := []
    glossedTokens := [("ŋuma", "father.ABS"), ("yabu-ŋgu", "mother-ERG"), ("bura-n", "see-NONFUT"), ("jaja-ŋgu", "child-ERG"), ("ŋamba-n", "hear-NONFUT")]
    translation := "Mother saw father and the child heard him."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "O"), ("second", "O"), ("derivation", "none")]
    comment := "Possibility (f), O₁ = O₂."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_28 : LinguisticExample :=
  { id := "dixon1994_28"
    source := ⟨"dixon-1994", "§6.2.2 (28)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma yabu-ŋgu bura-n (yabu-ŋgu) ŋamba-n"
    discourseSegments := []
    glossedTokens := [("ŋuma", "father.ABS"), ("yabu-ŋgu", "mother-ERG"), ("bura-n", "see-NONFUT"), ("(yabu-ŋgu)", "mother-ERG"), ("ŋamba-n", "hear-NONFUT")]
    translation := "Mother saw and heard father."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "O"), ("second", "O"), ("derivation", "none")]
    comment := "Possibility (j), O₁ = O₂ and A₁ = A₂: the pivot NP is the O; the A NP, always omittable, is understood as identical if unstated."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_32 : LinguisticExample :=
  { id := "dixon1994_32"
    source := ⟨"dixon-1994", "§6.2.2 (32)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma bural-ŋa-nyu yabu-gu"
    discourseSegments := []
    glossedTokens := [("ŋuma", "father.ABS"), ("bural-ŋa-nyu", "see-ANTIPASS-NONFUT"), ("yabu-gu", "mother-DAT")]
    translation := "Father saw mother."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "antipassive"), ("function", "S")]
    comment := "The antipassive version of (11) 'father saw mother', (31): underlying A into derived S, underlying O into dative."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_33 : LinguisticExample :=
  { id := "dixon1994_33"
    source := ⟨"dixon-1994", "§6.2.2 (33)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋana bural-ŋa-nyu nyurra-ŋgu"
    discourseSegments := []
    glossedTokens := [("ŋana", "we.all.NOM"), ("bural-ŋa-nyu", "see-ANTIPASS-NONFUT"), ("nyurra-ŋgu", "you.all-DAT")]
    translation := "We saw you all."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "antipassive"), ("function", "S")]
    comment := "The antipassive version of (16); dative is -ŋgu with pronouns."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_34 : LinguisticExample :=
  { id := "dixon1994_34"
    source := ⟨"dixon-1994", "§6.2.2 (34)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma banaga-nyu bural-ŋa-nyu yabu-gu"
    discourseSegments := []
    glossedTokens := [("ŋuma", "father.ABS"), ("banaga-nyu", "return-NONFUT"), ("bural-ŋa-nyu", "see-ANTIPASS-NONFUT"), ("yabu-gu", "mother-DAT")]
    translation := "Father returned and saw mother."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "S"), ("second", "A"), ("derivation", "antipassive")]
    comment := "Possibility (c), S₁ = A₂: the second clause is antipassivized to bring the underlying A into derived S and satisfy the S/O pivot."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_36 : LinguisticExample :=
  { id := "dixon1994_36"
    source := ⟨"dixon-1994", "§6.2.2 (36)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma jaja-ŋgu ŋamba-n bural-ŋa-nyu yabu-gu"
    discourseSegments := []
    glossedTokens := [("ŋuma", "father.ABS"), ("jaja-ŋgu", "child-ERG"), ("ŋamba-n", "hear-NONFUT"), ("bural-ŋa-nyu", "see-ANTIPASS-NONFUT"), ("yabu-gu", "mother-DAT")]
    translation := "The child heard father and he (father) saw mother."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "O"), ("second", "A"), ("derivation", "antipassive")]
    comment := "Possibility (h), O₁ = A₂, with the second clause antipassivized."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_39 : LinguisticExample :=
  { id := "dixon1994_39"
    source := ⟨"dixon-1994", "§6.2.2 (39)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma yabu-ŋgu ŋamba-n bural-ŋa-nyu yabu-gu"
    discourseSegments := []
    glossedTokens := [("ŋuma", "father.ABS"), ("yabu-ŋgu", "mother-ERG"), ("ŋamba-n", "hear-NONFUT"), ("bural-ŋa-nyu", "see-ANTIPASS-NONFUT"), ("yabu-gu", "mother-DAT")]
    translation := "Mother heard father and he saw her."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "O"), ("second", "A"), ("derivation", "antipassive")]
    comment := "Possibility (k), O₁ = A₂ and A₁ = O₂: the O₁ = A₂ NP is the pivot; the final dative NP cannot be omitted."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_42 : LinguisticExample :=
  { id := "dixon1994_42"
    source := ⟨"dixon-1994", "§6.2.2 (42)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma bural-ŋa-nyu yabu-gu banaga-nyu"
    discourseSegments := []
    glossedTokens := [("ŋuma", "father.ABS"), ("bural-ŋa-nyu", "see-ANTIPASS-NONFUT"), ("yabu-gu", "mother-DAT"), ("banaga-nyu", "return-NONFUT")]
    translation := "Father saw mother and returned."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "A"), ("second", "S"), ("derivation", "antipassive")]
    comment := "Possibility (e), A₁ = S₂, with the first clause antipassivized, which requires planning ahead; the -ŋurra construction of (46) is the alternative."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_44 : LinguisticExample :=
  { id := "dixon1994_44"
    source := ⟨"dixon-1994", "§6.2.2 (44)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma bural-ŋa-nyu yabu-gu jaja-ŋgu ŋamba-n"
    discourseSegments := []
    glossedTokens := [("ŋuma", "father.ABS"), ("bural-ŋa-nyu", "see-ANTIPASS-NONFUT"), ("yabu-gu", "mother-DAT"), ("jaja-ŋgu", "child-ERG"), ("ŋamba-n", "hear-NONFUT")]
    translation := "Father saw mother and the child heard him."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "A"), ("second", "O"), ("derivation", "antipassive")]
    comment := "Possibility (i), A₁ = O₂, with the first clause antipassivized."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_46 : LinguisticExample :=
  { id := "dixon1994_46"
    source := ⟨"dixon-1994", "§6.2.2 (46)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "yabu ŋuma-ŋgu bura-n (ŋuma) banaga-ŋurra"
    discourseSegments := []
    glossedTokens := [("yabu", "mother.ABS"), ("ŋuma-ŋgu", "father-ERG"), ("bura-n", "see-NONFUT"), ("(ŋuma)", "father.ABS"), ("banaga-ŋurra", "return-ŊURRA")]
    translation := "Father saw mother and then he immediately returned."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "A"), ("second", "S"), ("derivation", "ngurra")]
    comment := "The verbal inflection -ŋurra marks that the S or O of its clause is identical to the A of the preceding clause and that the event follows immediately; the common NP may be included or omitted."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_52 : LinguisticExample :=
  { id := "dixon1994_52"
    source := ⟨"dixon-1994", "§6.2.2 (52)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma bural-ŋa-nyu yabu-gu ŋambal-ŋa-nyu jaja-gu"
    discourseSegments := []
    glossedTokens := [("ŋuma", "father.ABS"), ("bural-ŋa-nyu", "see-ANTIPASS-NONFUT"), ("yabu-gu", "mother-DAT"), ("ŋambal-ŋa-nyu", "hear-ANTIPASS-NONFUT"), ("jaja-gu", "child-DAT")]
    translation := "Father saw mother and he heard the child."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "A"), ("second", "A"), ("derivation", "antipassive")]
    comment := "Possibility (g), A₁ = A₂: both clauses are antipassivized; alternatively only the second is, with the -ŋurra construction, (54)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_56 : LinguisticExample :=
  { id := "dixon1994_56"
    source := ⟨"dixon-1994", "§6.2.2 (56)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma banaga-nyu yabu-ŋgu bura-li"
    discourseSegments := []
    glossedTokens := [("ŋuma", "father.ABS"), ("banaga-nyu", "return-NONFUT"), ("yabu-ŋgu", "mother-ERG"), ("bura-li", "see-PURP")]
    translation := "Father returned in order for mother to see him; or father returned and as a result mother saw him."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "purposive"), ("first", "S"), ("second", "O"), ("derivation", "none")]
    comment := "Purposive coordination obeys the same S/O pivot: main and purposive clause must share an NP in S or O function in each, contrary to the expectation of §4.4 that purposive clauses group S with A."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_57 : LinguisticExample :=
  { id := "dixon1994_57"
    source := ⟨"dixon-1994", "§6.2.2 (57)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma banaga-nyu bural-ŋa-ygu yabu-gu"
    discourseSegments := []
    glossedTokens := [("ŋuma", "father.ABS"), ("banaga-nyu", "return-NONFUT"), ("bural-ŋa-ygu", "see-ANTIPASS-PURP"), ("yabu-gu", "mother-DAT")]
    translation := "Father returned in order to see mother; or father returned and as a result saw mother."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "purposive"), ("first", "S"), ("second", "A"), ("derivation", "antipassive")]
    comment := "The purposive clause is antipassivized to bring its A into derived S."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_59 : LinguisticExample :=
  { id := "dixon1994_59"
    source := ⟨"dixon-1994", "§6.2.2 (59)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "yabu ŋuma-ŋgu giga-n gubi-ŋgu mawa-li"
    discourseSegments := []
    glossedTokens := [("yabu", "mother.ABS"), ("ŋuma-ŋgu", "father-ERG"), ("giga-n", "tell.to.do-NONFUT"), ("gubi-ŋgu", "doctor-ERG"), ("mawa-li", "examine-PURP")]
    translation := "Father told mother to be examined by the doctor."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "purposive"), ("first", "O"), ("second", "O"), ("derivation", "none")]
    comment := "O₁ = O₂ with the verb 'tell to do'; the author corrects an earlier statement that the O of giga-l must be coreferential with the A or S of its purposive clause, fn. 19."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_60 : LinguisticExample :=
  { id := "dixon1994_60"
    source := ⟨"dixon-1994", "§6.2.2 (60)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "yabu ŋuma-ŋgu giga-n bural-ŋa-ygu jaja-gu"
    discourseSegments := []
    glossedTokens := [("yabu", "mother.ABS"), ("ŋuma-ŋgu", "father-ERG"), ("giga-n", "tell.to.do-NONFUT"), ("bural-ŋa-ygu", "see-ANTIPASS-PURP"), ("jaja-gu", "child-DAT")]
    translation := "Father told mother to look at the child."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "purposive"), ("first", "O"), ("second", "A"), ("derivation", "antipassive")]
    comment := "O₁ = A₂: the purposive clause must be antipassivized."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_61 : LinguisticExample :=
  { id := "dixon1994_61"
    source := ⟨"dixon-1994", "§6.2.2 (61)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma banaga-ŋu yabu-ŋgu bura-n"
    discourseSegments := []
    glossedTokens := [("ŋuma", "father.ABS"), ("banaga-ŋu", "return-REL.ABS"), ("yabu-ŋgu", "mother-ERG"), ("bura-n", "see-NONFUT")]
    translation := "Mother saw father who was returning."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "relative"), ("first", "O"), ("second", "S"), ("derivation", "none")]
    comment := "The common NP must be in S or O function within the relative clause; the relative verb bears -ŋu and a case inflection agreeing with the common NP in the main clause."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_62 : LinguisticExample :=
  { id := "dixon1994_62"
    source := ⟨"dixon-1994", "§6.2.2 (62)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "ŋuma yabu-ŋgu banaga-ŋu-rru bura-n"
    discourseSegments := []
    glossedTokens := [("ŋuma", "father.ABS"), ("yabu-ŋgu", "mother-ERG"), ("banaga-ŋu-rru", "return-REL-ERG"), ("bura-n", "see-NONFUT")]
    translation := "Mother, who was returning, saw father."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "relative"), ("first", "A"), ("second", "S"), ("derivation", "none")]
    comment := "The common NP may be in any core function in the main clause, here A, and the relative clause agrees in ergative case."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_63 : LinguisticExample :=
  { id := "dixon1994_63"
    source := ⟨"dixon-1994", "§6.2.2 (63)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "yabu bural-ŋa-ŋu ŋuma-gu banaga-nyu"
    discourseSegments := []
    glossedTokens := [("yabu", "mother.ABS"), ("bural-ŋa-ŋu", "see-ANTIPASS-REL.ABS"), ("ŋuma-gu", "father-DAT"), ("banaga-nyu", "return-NONFUT")]
    translation := "Mother, who saw father, was returning."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "relative"), ("first", "S"), ("second", "A"), ("derivation", "antipassive")]
    comment := "The common NP is in A function in the relative clause, so antipassive applies before relativisation."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_66 : LinguisticExample :=
  { id := "dixon1994_66"
    source := ⟨"dixon-1994", "§6.2.2 (66)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "yugu ŋuma-ŋgu balgal-ma-n yabu-gu"
    discourseSegments := []
    glossedTokens := [("yugu", "stick.ABS"), ("ŋuma-ŋgu", "father-ERG"), ("balgal-ma-n", "hit-INSTV-NONFUT"), ("yabu-gu", "mother-DAT")]
    translation := "Father used a stick to hit mother."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "instrumentive"), ("function", "O")]
    comment := "The instrumentive derivation places an underlying instrumental NP into derived O function, demoting the underlying O to dative, with -ma-l on the verb; it feeds the S/O pivot, (67) and (68)."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_68 : LinguisticExample :=
  { id := "dixon1994_68"
    source := ⟨"dixon-1994", "§6.2.2 (68)"⟩
    reportedIn := none
    language := "dyir1250"
    primaryText := "yugu ŋuma-ŋgu balgal-ma-ŋu yabu-gu jaja-ŋgu bura-n"
    discourseSegments := []
    glossedTokens := [("yugu", "stick.ABS"), ("ŋuma-ŋgu", "father-ERG"), ("balgal-ma-ŋu", "hit-INSTV-REL.ABS"), ("yabu-gu", "mother-DAT"), ("jaja-ŋgu", "child-ERG"), ("bura-n", "see-NONFUT")]
    translation := "The child saw the stick that was used by father to hit mother."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "relative"), ("first", "O"), ("second", "O"), ("derivation", "instrumentive")]
    comment := "The relative clause is first recast by the instrumentive derivation so that the common NP is in O function within it."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def en_a : LinguisticExample :=
  { id := "dixon1994_en_a"
    source := ⟨"dixon-1994", "§6.2.1 (a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill entered and sat down."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "S"), ("second", "S"), ("derivation", "none")]
    comment := "English's S/A pivot constrains omission of the second occurrence of a common NP, not clause linking itself: a weak pivot."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def en_b : LinguisticExample :=
  { id := "dixon1994_en_b"
    source := ⟨"dixon-1994", "§6.2.1 (b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill entered and was seen by Fred."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "S"), ("second", "O"), ("derivation", "passive")]
    comment := "S₁ = O₂: the second clause is passivized so that the common NP is in derived S."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def en_c : LinguisticExample :=
  { id := "dixon1994_en_c"
    source := ⟨"dixon-1994", "§6.2.1 (c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill entered and saw Fred."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "S"), ("second", "A"), ("derivation", "none")]
    comment := "S₁ = A₂."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def en_d : LinguisticExample :=
  { id := "dixon1994_en_d"
    source := ⟨"dixon-1994", "§6.2.1 (d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill was seen by Fred and laughed."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "O"), ("second", "S"), ("derivation", "passive")]
    comment := "O₁ = S₂: the first clause is passivized."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def en_e : LinguisticExample :=
  { id := "dixon1994_en_e"
    source := ⟨"dixon-1994", "§6.2.1 (e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fred saw Bill and laughed."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "A"), ("second", "S"), ("derivation", "none")]
    comment := "A₁ = S₂."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def en_f : LinguisticExample :=
  { id := "dixon1994_en_f"
    source := ⟨"dixon-1994", "§6.2.1 (f)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill was kicked by Tom and punched by Bob."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := [("Tom kicked and Bob punched Bill.", .acceptable)]
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "O"), ("second", "O"), ("derivation", "passive")]
    comment := "O₁ = O₂: both clauses are passivized; the alternative combines A-plus-verb from two clauses with the same O, which not all speakers accept."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def en_g : LinguisticExample :=
  { id := "dixon1994_en_g"
    source := ⟨"dixon-1994", "§6.2.1 (g)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bob kicked Jim and punched Bill."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "A"), ("second", "A"), ("derivation", "none")]
    comment := "A₁ = A₂."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def en_h : LinguisticExample :=
  { id := "dixon1994_en_h"
    source := ⟨"dixon-1994", "§6.2.1 (h)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bob was kicked by Tom and punched Bill."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "O"), ("second", "A"), ("derivation", "passive")]
    comment := "O₁ = A₂: the first clause is passivized."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def en_i : LinguisticExample :=
  { id := "dixon1994_en_i"
    source := ⟨"dixon-1994", "§6.2.1 (i)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bob punched Bill and was kicked by Tom."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "A"), ("second", "O"), ("derivation", "passive")]
    comment := "A₁ = O₂: the second clause is passivized."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def en_j : LinguisticExample :=
  { id := "dixon1994_en_j"
    source := ⟨"dixon-1994", "§6.2.1 (j)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fred punched and kicked Bill."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := [("Fred punched Bill and kicked him.", .acceptable)]
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "A"), ("second", "A"), ("derivation", "none")]
    comment := "O₁ = O₂ and A₁ = A₂: the verbs are coordinated so that each NP is stated once."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def en_k : LinguisticExample :=
  { id := "dixon1994_en_k"
    source := ⟨"dixon-1994", "§6.2.1 (k)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Fred punched Bill and was kicked by him."
    discourseSegments := []
    glossedTokens := []
    translation := ""
    context := ""
    judgment := .acceptable
    alternatives := [("Fred punched and was kicked by Bill.", .acceptable)]
    readings := []
    paperFeatures := [("construction", "coordination"), ("first", "A"), ("second", "O"), ("derivation", "passive")]
    comment := "O₁ = A₂ and A₁ = O₂: the A₁ = O₂ NP is the pivot and the second clause is passivized; not all speakers accept the alternative."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1_2_5, ex_1_2_7, ex_1_2_12, ex_15, ex_17, ex_19, ex_20, ex_21, ex_24, ex_28, ex_32, ex_33, ex_34, ex_36, ex_39, ex_42, ex_44, ex_46, ex_52, ex_56, ex_57, ex_59, ex_60, ex_61, ex_62, ex_63, ex_66, ex_68, en_a, en_b, en_c, en_d, en_e, en_f, en_g, en_h, en_i, en_j, en_k]

end Dixon1994.Examples
