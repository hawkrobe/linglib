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

def exp1_partwhole_the : LinguisticExample :=
  { id := "ahnzhu2025_exp1_partwhole_the"
    source := ⟨"ahn-zhu-2025", "UNVERIFIED Experiment 1, part-whole condition"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary bought a car. The steering wheel was too small."
    discourseSegments := ["Mary bought a car.", "The steering wheel was too small."]
    glossedTokens := []
    translation := "Mary bought a car. The steering wheel was too small."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "the"), ("bridging_type", "partWhole"), ("noun_arity", "sortal")]
    comment := "Migrated from Phenomena/Anaphora/Bridging.lean ahnZhuExp1PartWhole. Part-whole bridging baseline with the English definite article: 'the steering wheel' is licensed by the part-whole relation to 'a car'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def exp1_relational_the : LinguisticExample :=
  { id := "ahnzhu2025_exp1_relational_the"
    source := ⟨"ahn-zhu-2025", "UNVERIFIED Experiment 1, relational condition"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Mary bought a book. The author was very famous."
    discourseSegments := ["Mary bought a book.", "The author was very famous."]
    glossedTokens := []
    translation := "Mary bought a book. The author was very famous."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "the"), ("bridging_type", "relational"), ("noun_arity", "relational")]
    comment := "Migrated from Phenomena/Anaphora/Bridging.lean ahnZhuExp1Relational. Relational bridging baseline with the English definite article: 'the author' is licensed by the relational noun's internal argument bound to 'a book'."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def english_partwhole_that : LinguisticExample :=
  { id := "ahnzhu2025_english_partwhole_that"
    source := ⟨"ahn-zhu-2025", "UNVERIFIED English demonstrative, part-whole condition"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "?I saw a bicycle yesterday. That seat was broken."
    discourseSegments := ["I saw a bicycle yesterday.", "That seat was broken."]
    glossedTokens := []
    translation := "I saw a bicycle yesterday. That seat was broken."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "that"), ("bridging_type", "partWhole"), ("noun_arity", "sortal")]
    comment := "Migrated from Phenomena/Anaphora/Bridging.lean englishPartWholeThat. English demonstrative 'that' is degraded in part-whole bridging: the demonstrative requires discourse familiarity, which the bridged referent lacks."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def english_relational_that : LinguisticExample :=
  { id := "ahnzhu2025_english_relational_that"
    source := ⟨"ahn-zhu-2025", "UNVERIFIED English demonstrative, relational condition"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "?I read a book yesterday. That author was brilliant."
    discourseSegments := ["I read a book yesterday.", "That author was brilliant."]
    glossedTokens := []
    translation := "I read a book yesterday. That author was brilliant."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "that"), ("bridging_type", "relational"), ("noun_arity", "relational")]
    comment := "Migrated from Phenomena/Anaphora/Bridging.lean englishRelationalThat. English demonstrative 'that' is degraded in relational bridging."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def mandarin_partwhole_bare : LinguisticExample :=
  { id := "ahnzhu2025_mandarin_partwhole_bare"
    source := ⟨"ahn-zhu-2025", "UNVERIFIED Mandarin bare noun, part-whole condition"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "我昨天看见了一辆车。座椅坏了。"
    discourseSegments := ["我昨天看见了一辆车。", "座椅坏了。"]
    glossedTokens := []
    translation := "I saw a car yesterday. The seat was broken."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "bare"), ("bridging_type", "partWhole"), ("noun_arity", "sortal")]
    comment := "Migrated from Phenomena/Anaphora/Bridging.lean mandarinPartWholeBare. Mandarin bare noun bridges freely in the part-whole condition (uniqueness-mediated; not the relational-accommodation mechanism)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def mandarin_partwhole_na : LinguisticExample :=
  { id := "ahnzhu2025_mandarin_partwhole_na"
    source := ⟨"ahn-zhu-2025", "UNVERIFIED Mandarin na+CL, part-whole condition"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "我昨天看见了一辆车。那个座椅坏了。"
    discourseSegments := ["我昨天看见了一辆车。", "那个座椅坏了。"]
    glossedTokens := []
    translation := "I saw a car yesterday. That seat was broken."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "naCL"), ("bridging_type", "partWhole"), ("noun_arity", "sortal")]
    comment := "Migrated from Phenomena/Anaphora/Bridging.lean mandarinPartWholeNa. Mandarin na+CL is acceptable in part-whole bridging, unlike English 'that' — the contrast motivating Ahn & Zhu's relationalizing-operator analysis of na."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def mandarin_relational_bare : LinguisticExample :=
  { id := "ahnzhu2025_mandarin_relational_bare"
    source := ⟨"ahn-zhu-2025", "UNVERIFIED Mandarin bare noun, relational condition"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "我昨天读了一本书。作者很有名。"
    discourseSegments := ["我昨天读了一本书。", "作者很有名。"]
    glossedTokens := []
    translation := "I read a book yesterday. The author was famous."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "bare"), ("bridging_type", "relational"), ("noun_arity", "relational")]
    comment := "Migrated from Phenomena/Anaphora/Bridging.lean mandarinRelationalBare. Bare relational noun bridges: the lexically 2-place noun supplies the relatum slot (cf. relational_bare_can_bridge)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def mandarin_relational_na : LinguisticExample :=
  { id := "ahnzhu2025_mandarin_relational_na"
    source := ⟨"ahn-zhu-2025", "UNVERIFIED Mandarin na+CL, relational condition"⟩
    reportedIn := none
    language := "mand1415"
    primaryText := "我昨天读了一本书。那个作者很有名。"
    discourseSegments := ["我昨天读了一本书。", "那个作者很有名。"]
    glossedTokens := []
    translation := "I read a book yesterday. That author was famous."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("definite_form", "naCL"), ("bridging_type", "relational"), ("noun_arity", "relational")]
    comment := "Migrated from Phenomena/Anaphora/Bridging.lean mandarinRelationalNa. na+CL acceptable in relational bridging: na as relationalizing operator (Ahn & Zhu's analysis)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [exp1_partwhole_the, exp1_relational_the, english_partwhole_that, english_relational_that, mandarin_partwhole_bare, mandarin_partwhole_na, mandarin_relational_bare, mandarin_relational_na]

end AhnZhu2025.Examples
