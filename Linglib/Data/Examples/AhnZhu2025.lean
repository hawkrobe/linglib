import Linglib.Data.Examples.Schema

/-!
# `AhnZhu2025` — typed example data

Auto-generated from `Linglib/Data/Examples/AhnZhu2025.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace AhnZhu2025.Examples`.
-/

namespace AhnZhu2025.Examples

open Data.Examples

def md_partwhole_bare : LinguisticExample :=
  { id := "ahnzhu2025_md_partwhole_bare"
    source := ⟨"ahn-zhu-2025", "Study 3, part-whole, bare noun (cf. ex. 37)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "王雅雯正在用电脑。屏幕好像突然坏了。"
    discourseSegments := ["王雅雯正在用电脑。", "屏幕好像突然坏了。"]
    glossedTokens := []
    translation := "Wang Yawen is using the computer. The screen seemed to break all of a sudden."
    context := "Part-whole bridging: 'screen' is a part of the antecedent 'computer'."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "bare"), ("bridging_type", "partWhole"), ("noun_arity", "sortal")]
    comment := "Mandarin bare noun bridges freely in the part-whole condition (Studies 1 & 3). Licensed by situational uniqueness (Schwarz-weak / Jenks ι), not by the relatum-index route."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def md_partwhole_na : LinguisticExample :=
  { id := "ahnzhu2025_md_partwhole_na"
    source := ⟨"ahn-zhu-2025", "Study 3, part-whole, na+CL (cf. ex. 37)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "王雅雯正在用电脑。那块屏幕好像突然坏了。"
    discourseSegments := ["王雅雯正在用电脑。", "那块屏幕好像突然坏了。"]
    glossedTokens := []
    translation := "Wang Yawen is using the computer. That screen seemed to break all of a sudden."
    context := "Part-whole bridging with the demonstrative na+CL."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "naCL"), ("bridging_type", "partWhole"), ("noun_arity", "sortal")]
    comment := "Mandarin na+CL is acceptable in part-whole bridging, unlike English 'that' — the cross-linguistic contrast motivating the relationalizing-operator analysis of na (the demonstrative supplies a relatum via Barker's π, here the part-of relation)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def md_relational_bare : LinguisticExample :=
  { id := "ahnzhu2025_md_relational_bare"
    source := ⟨"ahn-zhu-2025", "Study 4, relational bridging, bare + relational noun (cf. ex. 59)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "王雅雯读了一本小说。作者很有名。"
    discourseSegments := ["王雅雯读了一本小说。", "作者很有名。"]
    glossedTokens := []
    translation := "Wang Yawen read a novel. The author is famous."
    context := "Relational bridging: 'author' is lexically relational to the antecedent 'novel'."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "bare"), ("bridging_type", "relational"), ("noun_arity", "relational")]
    comment := "Bare relational noun bridges (Study 4): the lexically 2-place noun 'author' supplies the relatum slot internally (covert possessor / argument-drop), so no external index (na) is needed."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def md_relational_na : LinguisticExample :=
  { id := "ahnzhu2025_md_relational_na"
    source := ⟨"ahn-zhu-2025", "Study 4, relational bridging, na+CL + relational noun (cf. ex. 59)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "王雅雯读了一本小说。那位作者很有名。"
    discourseSegments := ["王雅雯读了一本小说。", "那位作者很有名。"]
    glossedTokens := []
    translation := "Wang Yawen read a novel. That author is famous."
    context := "Relational bridging with the demonstrative na+CL and a relational noun."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "naCL"), ("bridging_type", "relational"), ("noun_arity", "relational")]
    comment := "na+CL acceptable in relational bridging: na relationalizes via π and binds the external relatum to the antecedent (Ahn & Zhu's analysis)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def md_nonrel_bare : LinguisticExample :=
  { id := "ahnzhu2025_md_nonrel_bare"
    source := ⟨"ahn-zhu-2025", "Study 4, relational bridging, bare + NON-relational noun (cf. ex. 59)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "王雅雯读了一本小说。?小说家很有名。"
    discourseSegments := ["王雅雯读了一本小说。", "?小说家很有名。"]
    glossedTokens := []
    translation := "Wang Yawen read a novel. The novelist is famous."
    context := "Relational bridging where the bridged noun 'novelist' is NOT lexically relational."
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "bare"), ("bridging_type", "relational"), ("noun_arity", "sortal")]
    comment := "THE crucial Study-4 cell, borne out: a bare noun licenses relational bridging ONLY if the noun is lexically relational. 'Novelist' is non-relational (sortal), so the bare form is degraded (rated significantly lower than na+novelist and than bare+author; ~4.82/7). It has no slot to host the relatum the bridge requires."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def md_nonrel_na : LinguisticExample :=
  { id := "ahnzhu2025_md_nonrel_na"
    source := ⟨"ahn-zhu-2025", "Study 4, relational bridging, na+CL + NON-relational noun (cf. ex. 59)"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "王雅雯读了一本小说。那位小说家很有名。"
    discourseSegments := ["王雅雯读了一本小说。", "那位小说家很有名。"]
    glossedTokens := []
    translation := "Wang Yawen read a novel. That novelist is famous."
    context := "Relational bridging with na+CL and a non-relational bridged noun."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "naCL"), ("bridging_type", "relational"), ("noun_arity", "sortal")]
    comment := "Study 4: na+CL licenses relational bridging REGARDLESS of the noun's lexical relationality — na itself is the relationalizer that introduces the external relatum, so even a non-relational noun ('novelist') bridges. This is the prediction that distinguishes the relationalizer account from a lexical-relation account."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def eng_partwhole_the : LinguisticExample :=
  { id := "ahnzhu2025_eng_partwhole_the"
    source := ⟨"ahn-zhu-2025", "Study 2, part-whole, definite 'the' (cf. ex. 20a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary bought a house. The roof needed to be replaced."
    discourseSegments := ["Mary bought a house.", "The roof needed to be replaced."]
    glossedTokens := []
    translation := "Mary bought a house. The roof needed to be replaced."
    context := "Part-whole bridging with the English definite article."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "the"), ("bridging_type", "partWhole"), ("noun_arity", "sortal")]
    comment := "English definite descriptions bridge freely (Study 2 baseline)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def eng_partwhole_that : LinguisticExample :=
  { id := "ahnzhu2025_eng_partwhole_that"
    source := ⟨"ahn-zhu-2025", "Study 2, part-whole, demonstrative 'that' (cf. ex. 20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary bought a house. ?That roof needed to be replaced."
    discourseSegments := ["Mary bought a house.", "?That roof needed to be replaced."]
    glossedTokens := []
    translation := "Mary bought a house. That roof needed to be replaced."
    context := "Part-whole bridging with the English demonstrative."
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "that"), ("bridging_type", "partWhole"), ("noun_arity", "sortal")]
    comment := "English demonstratives are significantly DEGRADED in bridging (Study 2), but NOT categorically ungrammatical — mean ratings ~4.3/7, well above the ~1.9-2.3 of odd controls. Ahn & Zhu analyze this as economy-based competition (the demonstrative is blocked-but-available because the definite can do the job), not a hard constraint. Hence .marginal, not .unacceptable."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def eng_relational_the : LinguisticExample :=
  { id := "ahnzhu2025_eng_relational_the"
    source := ⟨"ahn-zhu-2025", "Study 2, relational, definite 'the'"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Grace bought a CD. The singer became famous."
    discourseSegments := ["Grace bought a CD.", "The singer became famous."]
    glossedTokens := []
    translation := "Grace bought a CD. The singer became famous."
    context := "Relational bridging with the English definite article ('singer' relational to 'CD')."
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "the"), ("bridging_type", "relational"), ("noun_arity", "relational")]
    comment := "English definite descriptions bridge freely in the relational condition too (Study 2 baseline; cf. the Fig. 5 sample item)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def eng_relational_that : LinguisticExample :=
  { id := "ahnzhu2025_eng_relational_that"
    source := ⟨"ahn-zhu-2025", "Study 2, relational, demonstrative 'that'"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Grace bought a CD. ?That singer became famous."
    discourseSegments := ["Grace bought a CD.", "?That singer became famous."]
    glossedTokens := []
    translation := "Grace bought a CD. That singer became famous."
    context := "Relational bridging with the English demonstrative."
    judgment := .marginal
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "that"), ("bridging_type", "relational"), ("noun_arity", "relational")]
    comment := "English demonstratives are degraded for relational bridging too (Study 2), though rated higher than for part-whole (~5.0/7); still significantly below the definite. Economy-blocked, not ungrammatical (.marginal)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [md_partwhole_bare, md_partwhole_na, md_relational_bare, md_relational_na, md_nonrel_bare, md_nonrel_na, eng_partwhole_the, eng_partwhole_that, eng_relational_the, eng_relational_that]

end AhnZhu2025.Examples
