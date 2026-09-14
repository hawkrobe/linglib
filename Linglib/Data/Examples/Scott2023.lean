import Linglib.Data.Examples.Schema

/-!
# `Scott2023` — typed example data

Auto-generated from `Linglib/Data/Examples/Scott2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace Scott2023.Examples`.
-/

namespace Scott2023.Examples

open Data.Examples

def ex_78a : LinguisticExample :=
  { id := "scott2023_78a"
    source := ⟨"scott-2023", "(78a)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma qo b'et *qo'=y."
    discourseSegments := []
    glossedTokens := [("Ma", "PROX"), ("qo", "B1PL"), ("b'et", "walk"), ("qo'=y", "1PL=DISAGR")]
    translation := "We (exclusive) walked."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("position", "S"), ("cell", "1plExcl"), ("morphemes", "qo=i")]
    comment := "The full first-person plural pronoun is out as an intransitive subject agreed with by Infl."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_78b : LinguisticExample :=
  { id := "scott2023_78b"
    source := ⟨"scott-2023", "(78b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma ∅ kub' q-tz'ib'-an *qo'=y."
    discourseSegments := []
    glossedTokens := [("Ma", "PROX"), ("∅", "B2/3SG"), ("kub'", "DIR:down"), ("q-tz'ib'-an", "A1PL-write-DS"), ("qo'=y", "1PL=DISAGR")]
    translation := "We (exclusive) wrote it down."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("position", "A"), ("cell", "1plExcl"), ("morphemes", "qo=i")]
    comment := "The full first-person plural pronoun is out as a transitive subject agreed with by Voice."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_78c : LinguisticExample :=
  { id := "scott2023_78c"
    source := ⟨"scott-2023", "(78c)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "q-lan *qo'=y"
    discourseSegments := []
    glossedTokens := [("q-lan", "A1PL-wool.thread"), ("qo'=y", "1PL=DISAGR")]
    translation := "our (exclusive) wool thread"
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("position", "possessor"), ("cell", "1plExcl"), ("morphemes", "qo=i")]
    comment := "The full first-person plural pronoun is out as a possessor agreed with by Poss."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_79 : LinguisticExample :=
  { id := "scott2023_79"
    source := ⟨"scott-2023", "(79)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "B'et qo'=y."
    discourseSegments := []
    glossedTokens := [("B'et", "walk"), ("qo'=y", "1PL=DISAGR")]
    translation := "We (exclusive) walked."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "unagreed"), ("cell", "1plExcl"), ("morphemes", "qo=i")]
    comment := "With no agreement on the predicate the full pronoun is in."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_68b : LinguisticExample :=
  { id := "scott2023_68b"
    source := ⟨"scott-2023", "(68b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "O qo tan=i."
    discourseSegments := []
    glossedTokens := [("O", "PFV"), ("qo", "B1PL"), ("tan", "sleep"), ("=i", "=DISAGR")]
    translation := "We (exclusive) slept."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "S"), ("cell", "1plExcl"), ("morphemes", "=i")]
    comment := "The reduced first-person plural subject pronoun: the disagreement enclitic alone."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_85a : LinguisticExample :=
  { id := "scott2023_85a"
    source := ⟨"scott-2023", "(85a)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma chin b'et *qin=i."
    discourseSegments := []
    glossedTokens := [("Ma", "PROX"), ("chin", "B1SG"), ("b'et", "walk"), ("qin=i", "1SG=DISAGR")]
    translation := "I walked."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("position", "S"), ("cell", "1sg"), ("morphemes", "qin=i")]
    comment := "The full first-person singular pronoun is out as an intransitive subject."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_85b : LinguisticExample :=
  { id := "scott2023_85b"
    source := ⟨"scott-2023", "(85b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma ∅ kub' n-tz'ib'-an *qin=i."
    discourseSegments := []
    glossedTokens := [("Ma", "PROX"), ("∅", "B2/3SG"), ("kub'", "DIR:down"), ("n-tz'ib'-an", "A1SG-write-DS"), ("qin=i", "1SG=DISAGR")]
    translation := "I wrote it down."
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("position", "A"), ("cell", "1sg"), ("morphemes", "qin=i")]
    comment := "The full first-person singular pronoun is out as a transitive subject."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_85c : LinguisticExample :=
  { id := "scott2023_85c"
    source := ⟨"scott-2023", "(85c)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "n-lan *qin=i"
    discourseSegments := []
    glossedTokens := [("n-lan", "A1SG-wool.thread"), ("qin=i", "1SG=DISAGR")]
    translation := "my wool thread"
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("position", "possessor"), ("cell", "1sg"), ("morphemes", "qin=i")]
    comment := "The full first-person singular pronoun is out as a possessor."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_62 : LinguisticExample :=
  { id := "scott2023_62"
    source := ⟨"scott-2023", "(62)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma chin b'et=i."
    discourseSegments := []
    glossedTokens := [("Ma", "PROX"), ("chin", "B1SG"), ("b'et", "walk"), ("=i", "=DISAGR")]
    translation := "I walked."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "S"), ("cell", "1sg"), ("morphemes", "=i")]
    comment := "Agreeing Set B on Infl and the reduced first-person singular subject pronoun."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_86a : LinguisticExample :=
  { id := "scott2023_86a"
    source := ⟨"scott-2023", "(86a)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma chi b'et q=i."
    discourseSegments := []
    glossedTokens := [("Ma", "PROX"), ("chi", "B2/3PL"), ("b'et", "walk"), ("q=i", "2PL=DISAGR")]
    translation := "Y'all walked."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "S"), ("cell", "2pl"), ("morphemes", "q=i")]
    comment := "Second-person plural subjects keep their full form."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_86b : LinguisticExample :=
  { id := "scott2023_86b"
    source := ⟨"scott-2023", "(86b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma ∅ kub' ky-tz'ib'-an q=i."
    discourseSegments := []
    glossedTokens := [("Ma", "PROX"), ("∅", "B2/3SG"), ("kub'", "DIR:down"), ("ky-tz'ib'-an", "A2/3PL-write-DS"), ("q=i", "2PL=DISAGR")]
    translation := "Y'all wrote it down."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "A"), ("cell", "2pl"), ("morphemes", "q=i")]
    comment := "Second-person plural transitive subjects keep their full form."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_86c : LinguisticExample :=
  { id := "scott2023_86c"
    source := ⟨"scott-2023", "(86c)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "ky-lan q=i"
    discourseSegments := []
    glossedTokens := [("ky-lan", "A2/3PL-wool.thread"), ("q=i", "2PL=DISAGR")]
    translation := "y'all's wool thread"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "possessor"), ("cell", "2pl"), ("morphemes", "q=i")]
    comment := "Second-person plural possessors keep their full form."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_87a : LinguisticExample :=
  { id := "scott2023_87a"
    source := ⟨"scott-2023", "(87a)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma chi b'et qa."
    discourseSegments := []
    glossedTokens := [("Ma", "PROX"), ("chi", "B2/3PL"), ("b'et", "walk"), ("qa", "PL")]
    translation := "They walked."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "S"), ("cell", "3pl"), ("morphemes", "qa")]
    comment := "Third-person plural subjects keep their full form."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_87b : LinguisticExample :=
  { id := "scott2023_87b"
    source := ⟨"scott-2023", "(87b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma ∅ kub' ky-tz'ib'-an qa."
    discourseSegments := []
    glossedTokens := [("Ma", "PROX"), ("∅", "B2/3SG"), ("kub'", "DIR:down"), ("ky-tz'ib'-an", "A2/3PL-write-DS"), ("qa", "PL")]
    translation := "They wrote it down."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "A"), ("cell", "3pl"), ("morphemes", "qa")]
    comment := "Third-person plural transitive subjects keep their full form."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_87c : LinguisticExample :=
  { id := "scott2023_87c"
    source := ⟨"scott-2023", "(87c)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "ky-lan qa"
    discourseSegments := []
    glossedTokens := [("ky-lan", "A2/3PL-wool.thread"), ("qa", "PL")]
    translation := "their wool thread"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "possessor"), ("cell", "3pl"), ("morphemes", "qa")]
    comment := "Third-person plural possessors keep their full form."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_88b : LinguisticExample :=
  { id := "scott2023_88b"
    source := ⟨"scott-2023", "(88b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "B'et qin=i."
    discourseSegments := []
    glossedTokens := [("B'et", "walk"), ("qin=i", "1SG=DISAGR")]
    translation := "I walked."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "unagreed"), ("cell", "1sg"), ("morphemes", "qin=i")]
    comment := "Without agreement the first-person singular pronoun is full."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_88c : LinguisticExample :=
  { id := "scott2023_88c"
    source := ⟨"scott-2023", "(88c)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "B'et q=i."
    discourseSegments := []
    glossedTokens := [("B'et", "walk"), ("q=i", "2PL=DISAGR")]
    translation := "Y'all walked."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "unagreed"), ("cell", "2pl"), ("morphemes", "q=i")]
    comment := "Without agreement the second-person plural pronoun is full."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_88d : LinguisticExample :=
  { id := "scott2023_88d"
    source := ⟨"scott-2023", "(88d)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "B'et qa."
    discourseSegments := []
    glossedTokens := [("B'et", "walk"), ("qa", "PL")]
    translation := "They walked."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "unagreed"), ("cell", "3pl"), ("morphemes", "qa")]
    comment := "Without agreement the third-person plural pronoun is full."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_69a : LinguisticExample :=
  { id := "scott2023_69a"
    source := ⟨"scott-2023", "(69a)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma tz'=ok ky-ke'y-an qa qin=i."
    discourseSegments := []
    glossedTokens := [("Ma", "PROX"), ("tz'=ok", "B2/3SG=DIR:in"), ("ky-ke'y-an", "A2/3PL-see-DS"), ("qa", "PL"), ("qin=i", "1SG=DISAGR")]
    translation := "They saw me."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "object"), ("cell", "1sg"), ("morphemes", "qin=i")]
    comment := "A transitive object is a full pronoun, next to default Set B on Infl."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_89a : LinguisticExample :=
  { id := "scott2023_89a"
    source := ⟨"scott-2023", "(89a)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "ky-ja q=i"
    discourseSegments := []
    glossedTokens := [("ky-ja", "A2/3PL-house"), ("q=i", "2PL=DISAGR")]
    translation := "y'all's house"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "possessor"), ("cell", "2pl"), ("morphemes", "q=i")]
    comment := "The full second-person plural possessor."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_89b : LinguisticExample :=
  { id := "scott2023_89b"
    source := ⟨"scott-2023", "(89b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "ky-ja=y"
    discourseSegments := []
    glossedTokens := [("ky-ja", "A2/3PL-house"), ("=y", "=DISAGR")]
    translation := "y'all's house"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "possessor"), ("cell", "2pl"), ("morphemes", "=i"), ("optionalReduction", "yes")]
    comment := "The optionally reduced second-person plural possessor, a Set A context."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_90b : LinguisticExample :=
  { id := "scott2023_90b"
    source := ⟨"scott-2023", "(90b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma ∅ tzaj ky-q'ama-'n=i w-i=y."
    discourseSegments := []
    glossedTokens := [("Ma", "PROX"), ("∅", "B2/3SG"), ("tzaj", "DIR:come"), ("ky-q'ama-'n", "A2/3PL-tell-DS"), ("=i", "=DISAGR"), ("w-i=y", "A1SG-RN:dat=DISAGR")]
    translation := "Y'all told me."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "A"), ("cell", "2pl"), ("morphemes", "=i"), ("optionalReduction", "yes")]
    comment := "The optionally reduced second-person plural transitive subject, a Set A context."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_91a : LinguisticExample :=
  { id := "scott2023_91a"
    source := ⟨"scott-2023", "(91a)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma chi b'ix-an q=i."
    discourseSegments := []
    glossedTokens := [("Ma", "PROX"), ("chi", "B2/3PL"), ("b'ix-an", "dance-DS"), ("q=i", "2PL=DISAGR")]
    translation := "Y'all danced."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "S"), ("cell", "2pl"), ("morphemes", "q=i")]
    comment := "A second-person plural intransitive subject, a Set B context."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_91b : LinguisticExample :=
  { id := "scott2023_91b"
    source := ⟨"scott-2023", "(91b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "#Ma chi b'ix-n=i."
    discourseSegments := []
    glossedTokens := [("Ma", "PROX"), ("chi", "B2/3PL"), ("b'ix-n", "dance-DS"), ("=i", "=DISAGR")]
    translation := "Y'all danced."
    context := ""
    judgment := .unacceptable
    alternatives := []
    readings := []
    paperFeatures := [("position", "S"), ("cell", "2pl"), ("morphemes", "=i")]
    comment := "Reduction of the second-person plural is not available in a Set B context; the sentence is read as 'I danced'."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_57 : LinguisticExample :=
  { id := "scott2023_57"
    source := ⟨"scott-2023", "(57)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma chn=ok t-ke'y-an Mintz."
    discourseSegments := []
    glossedTokens := [("Ma", "PROX"), ("chn=ok", "B1SG=DIR:in"), ("t-ke'y-an", "A2/3SG-see-DS"), ("Mintz", "Mintz")]
    translation := "Mintz saw me."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "agreeingObject"), ("cell", "1sg"), ("setB", "chin")]
    comment := "The agreeing-object pattern of standard Mam, available to some speakers as a formal variant: Infl's probe is satisfied by φ alone."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_59 : LinguisticExample :=
  { id := "scott2023_59"
    source := ⟨"scott-2023", "(59)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Ma tz'=ok t-ke'y-an Mintz qin=i."
    discourseSegments := []
    glossedTokens := [("Ma", "PROX"), ("tz'=ok", "B2/3SG=DIR:in"), ("t-ke'y-an", "A2/3SG-see-DS"), ("Mintz", "Mintz"), ("qin=i", "1SG=DISAGR")]
    translation := "Mintz saw me."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "defaultObject"), ("cell", "1sg"), ("setB", "tz'")]
    comment := "Default Set B: Infl's probe halts at transitive Voice, and the object is a full pronoun."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_73 : LinguisticExample :=
  { id := "scott2023_73"
    source := ⟨"scott-2023", "(73)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Taj w-ul=i …"
    discourseSegments := []
    glossedTokens := [("Taj", "when"), ("w-ul", "A1SG-arrive"), ("=i", "=DISAGR")]
    translation := "When I arrived …"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "superExtendedErgative"), ("position", "S"), ("cell", "1sg"), ("setA", "w")]
    comment := "Extended ergativity: the intransitive subject of a when-clause takes Set A."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_77a : LinguisticExample :=
  { id := "scott2023_77a"
    source := ⟨"scott-2023", "(77a)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "Taj t-ok t-ke'y-an=i qin=i …"
    discourseSegments := []
    glossedTokens := [("Taj", "when"), ("t-ok", "A2/3SG-DIR:in"), ("t-ke'y-an", "A2/3SG-see-DS"), ("=i", "=DISAGR"), ("qin=i", "1SG=DISAGR")]
    translation := "When you saw me …"
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("construction", "superExtendedErgative"), ("position", "object"), ("cell", "1sg"), ("setA", "t")]
    comment := "Super-extended ergativity: the object slot on the directional takes only the default Set A, and the object is a full pronoun."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_77b : LinguisticExample :=
  { id := "scott2023_77b"
    source := ⟨"scott-2023", "(77b)"⟩
    reportedIn := none
    language := "mamm1241"
    primaryText := "*Taj w-ok t-ke'y-an=i …"
    discourseSegments := []
    glossedTokens := [("Taj", "when"), ("w-ok", "A1SG-DIR:in"), ("t-ke'y-an", "A2/3SG-see-DS"), ("=i", "=DISAGR")]
    translation := "When you saw me …"
    context := ""
    judgment := .ungrammatical
    alternatives := []
    readings := []
    paperFeatures := [("construction", "superExtendedErgative"), ("position", "object"), ("cell", "1sg"), ("setA", "w")]
    comment := "Agreeing Set A for the object is out in a super-extended ergative clause."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def all : List LinguisticExample := [ex_78a, ex_78b, ex_78c, ex_79, ex_68b, ex_85a, ex_85b, ex_85c, ex_62, ex_86a, ex_86b, ex_86c, ex_87a, ex_87b, ex_87c, ex_88b, ex_88c, ex_88d, ex_69a, ex_89a, ex_89b, ex_90b, ex_91a, ex_91b, ex_57, ex_59, ex_73, ex_77a, ex_77b]

end Scott2023.Examples
