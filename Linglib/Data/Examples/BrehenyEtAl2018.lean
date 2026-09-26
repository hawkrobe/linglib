module

public import Linglib.Data.Examples.Schema

/-!
# `BrehenyEtAl2018` — typed example data

Auto-generated from `Linglib/Data/Examples/BrehenyEtAl2018.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace BrehenyEtAl2018.Examples`.
-/

@[expose] public section

namespace BrehenyEtAl2018.Examples

open Data.Examples

def ex_1 : LinguisticExample :=
  { id := "brehenyetal2018_1"
    source := ⟨"breheny-et-al-2018", "(1)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John did some of the homework."
    discourseSegments := []
    glossedTokens := []
    translation := "John did some of the homework."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: John didn't do all of the homework", .acceptable), ("inference: John did all of the homework", .unacceptable)]
    paperFeatures := [("case", "direct"), ("prejacent", "some"), ("alternative", "all"), ("symmetric alternative", "some but not all")]
    comment := "The symmetric alternative (2), some but not all, must not enter the computation."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_11 : LinguisticExample :=
  { id := "brehenyetal2018_11"
    source := ⟨"breheny-et-al-2018", "(11)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "He smoked pot."
    discourseSegments := []
    glossedTokens := []
    translation := "He smoked pot."
    context := "Mary got drunk. What did John do?"
    judgment := .acceptable
    alternatives := []
    readings := [("inference: John didn't get drunk", .acceptable)]
    paperFeatures := [("case", "particularised"), ("prejacent", "smoked pot"), ("alternative", "got drunk")]
    comment := "The alternative is formal because got drunk is salient in the context."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_12 : LinguisticExample :=
  { id := "brehenyetal2018_12"
    source := ⟨"breheny-et-al-2018", "(12)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't do all of the homework."
    discourseSegments := []
    glossedTokens := []
    translation := "John didn't do all of the homework."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: John did some of the homework", .acceptable)]
    paperFeatures := [("case", "indirect"), ("prejacent", "not all"), ("alternative", "not any"), ("symmetric alternative", "some")]
    comment := "The inference negates (13), John didn't do any of the homework; the structural approach also derives some, (14)–(15)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_17 : LinguisticExample :=
  { id := "brehenyetal2018_17"
    source := ⟨"breheny-et-al-2018", "(17)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John (my favourite student) didn't do all of the homework."
    discourseSegments := []
    glossedTokens := []
    translation := "John (my favourite student) didn't do all of the homework."
    context := "What happened at school today?"
    judgment := .acceptable
    alternatives := []
    readings := [("inference: John did some of the homework", .acceptable)]
    paperFeatures := [("case", "indirect"), ("prejacent", "not all"), ("focus", "broad")]
    comment := "Focus includes negation, so narrow focus cannot keep some out of the alternatives."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_18 : LinguisticExample :=
  { id := "brehenyetal2018_18"
    source := ⟨"trinh-haida-2015", "(5)"⟩
    reportedIn := some ⟨"breheny-et-al-2018", "(18)"⟩
    language := "stan1293"
    primaryText := "John went for a run."
    discourseSegments := []
    glossedTokens := []
    translation := "John went for a run."
    context := "Bill went for a run and didn't smoke. What did John do?"
    judgment := .acceptable
    alternatives := []
    readings := [("inference: John smoked", .acceptable)]
    paperFeatures := [("case", "particularised"), ("prejacent", "run"), ("alternative", "run and not smoke"), ("symmetric alternative", "run and smoke")]
    comment := "Unnatural when it is known that John didn't smoke."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_28 : LinguisticExample :=
  { id := "brehenyetal2018_28"
    source := ⟨"breheny-et-al-2018", "(28)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John went for a run."
    discourseSegments := []
    glossedTokens := []
    translation := "John went for a run."
    context := "Bill went for a run. He didn't smoke. What did John do?"
    judgment := .acceptable
    alternatives := []
    readings := [("inference: John smoked", .acceptable)]
    paperFeatures := [("case", "particularised"), ("prejacent", "run"), ("alternative", "not smoke"), ("symmetric alternative", "smoke")]
    comment := "The conjunction is split across sentences, so no salient constituent means run and not smoke, (29)–(31)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_32 : LinguisticExample :=
  { id := "brehenyetal2018_32"
    source := ⟨"breheny-et-al-2018", "(32)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not the case that the glass is full."
    discourseSegments := []
    glossedTokens := []
    translation := "It's not the case that the glass is full."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: the glass is not empty", .acceptable), ("inference: the glass is empty", .unacceptable)]
    paperFeatures := [("case", "gradable adjective"), ("prejacent", "not full"), ("alternative", "not empty"), ("symmetric alternative", "empty")]
    comment := "Sentential negation keeps the Atomicity Constraint from blocking not empty, footnote 17."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_33 : LinguisticExample :=
  { id := "brehenyetal2018_33"
    source := ⟨"breheny-et-al-2018", "(33)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not the case that the glass is empty."
    discourseSegments := []
    glossedTokens := []
    translation := "It's not the case that the glass is empty."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: the glass is not full", .acceptable), ("inference: the glass is full", .unacceptable)]
    paperFeatures := [("case", "gradable adjective"), ("prejacent", "not empty"), ("alternative", "not full"), ("symmetric alternative", "full")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_34 : LinguisticExample :=
  { id := "brehenyetal2018_34"
    source := ⟨"breheny-et-al-2018", "(34)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not the case that a tie is required."
    discourseSegments := []
    glossedTokens := []
    translation := "It's not the case that a tie is required."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: a tie is allowed", .acceptable), ("inference: a tie is mandatory", .unacceptable)]
    paperFeatures := [("case", "gradable adjective"), ("prejacent", "not required"), ("alternative", "not allowed")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_35 : LinguisticExample :=
  { id := "brehenyetal2018_35"
    source := ⟨"breheny-et-al-2018", "(35)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "It's not the case that Mary's promotion is certain."
    discourseSegments := []
    glossedTokens := []
    translation := "It's not the case that Mary's promotion is certain."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: Mary's promotion is possible", .acceptable), ("inference: Mary's promotion is impossible", .unacceptable)]
    paperFeatures := [("case", "gradable adjective"), ("prejacent", "not certain"), ("alternative", "not possible")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_38a : LinguisticExample :=
  { id := "brehenyetal2018_38a"
    source := ⟨"breheny-et-al-2018", "(38a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "This neighbourhood is not safe."
    discourseSegments := []
    glossedTokens := []
    translation := "This neighbourhood is not safe."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: this neighbourhood is not dangerous", .unacceptable)]
    paperFeatures := [("case", "gradable adjective"), ("prejacent", "not safe"), ("scale", "upper closed")]
    comment := "The modifier route (37) predicts the inference; it is absent."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_38b : LinguisticExample :=
  { id := "brehenyetal2018_38b"
    source := ⟨"breheny-et-al-2018", "(38b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John is not tall."
    discourseSegments := []
    glossedTokens := []
    translation := "John is not tall."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: John is not small", .unacceptable)]
    paperFeatures := [("case", "gradable adjective"), ("prejacent", "not tall"), ("scale", "open")]
    comment := ""
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_38c : LinguisticExample :=
  { id := "brehenyetal2018_38c"
    source := ⟨"breheny-et-al-2018", "(38c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The glass is not transparent."
    discourseSegments := []
    glossedTokens := []
    translation := "The glass is not transparent."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: the glass is not opaque", .unacceptable)]
    paperFeatures := [("case", "gradable adjective"), ("prejacent", "not transparent"), ("scale", "closed")]
    comment := "Transparent takes the same modifiers as full, so scale structure does not explain the contrast with (32)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_41 : LinguisticExample :=
  { id := "brehenyetal2018_41"
    source := ⟨"breheny-et-al-2018", "(41)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "John-wa ki-te yoi."
    discourseSegments := []
    glossedTokens := [("John-wa", "John-TOP"), ("ki-te", "come-GER"), ("yoi", "good")]
    translation := "John is allowed to come."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: John is not required to come", .acceptable)]
    paperFeatures := [("case", "too few lexical alternatives"), ("prejacent", "allowed"), ("alternative", "required")]
    comment := "Deontic possibility with the adjective yoi; unnatural when John is required to come."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_42a : LinguisticExample :=
  { id := "brehenyetal2018_42a"
    source := ⟨"breheny-et-al-2018", "(42a)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "John-wa ko-naku-te-wa nar-anai."
    discourseSegments := []
    glossedTokens := [("John-wa", "John-TOP"), ("ko-naku-te-wa", "come-NEG-GER-TOP"), ("nar-anai", "become-NEG")]
    translation := "John must come."
    context := ""
    judgment := .acceptable
    alternatives := [("John-wa ko-naku-te-wa ike-nai.", .acceptable)]
    readings := []
    paperFeatures := [("case", "too few lexical alternatives"), ("prejacent", "required")]
    comment := "Deontic necessity with a negated verbal stem, nar-anai or ike-nai, and obligatory topic marking on the gerund: not derivable from (41) by substitution and deletion."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_42b : LinguisticExample :=
  { id := "brehenyetal2018_42b"
    source := ⟨"breheny-et-al-2018", "(42b)"⟩
    reportedIn := none
    language := "nucl1643"
    primaryText := "John-wa kuru hitsuyoo-ga aru."
    discourseSegments := []
    glossedTokens := [("John-wa", "John-TOP"), ("kuru", "come"), ("hitsuyoo-ga", "necessity-NOM"), ("aru", "exist")]
    translation := "John needs to come."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("case", "too few lexical alternatives"), ("prejacent", "required")]
    comment := "Deontic necessity as an existential construction over the nominal hitsuyoo."
    metaLanguage := "stan1293"
    lgrConformance := "MORPHEME_ALIGNED" }

def ex_44 : LinguisticExample :=
  { id := "brehenyetal2018_44"
    source := ⟨"swanson-2010", ""⟩
    reportedIn := some ⟨"breheny-et-al-2018", "(44)"⟩
    language := "stan1293"
    primaryText := "Going to confession is permitted."
    discourseSegments := []
    glossedTokens := []
    translation := "Going to confession is permitted."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: going to confession is optional", .acceptable), ("inference: going to confession is required", .unacceptable)]
    paperFeatures := [("case", "too many lexical alternatives"), ("prejacent", "permitted"), ("alternative", "required"), ("symmetric alternative", "optional")]
    comment := "Optional is a single lexical item of the same complexity as required."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_45 : LinguisticExample :=
  { id := "brehenyetal2018_45"
    source := ⟨"swanson-2010", ""⟩
    reportedIn := some ⟨"breheny-et-al-2018", "(45)"⟩
    language := "stan1293"
    primaryText := "The heater sometimes squeaks."
    discourseSegments := []
    glossedTokens := []
    translation := "The heater sometimes squeaks."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: the heater intermittently squeaks", .acceptable), ("inference: the heater constantly squeaks", .unacceptable)]
    paperFeatures := [("case", "too many lexical alternatives"), ("prejacent", "sometimes"), ("alternative", "constantly"), ("symmetric alternative", "intermittently")]
    comment := "Footnote 23 weighs whether intermittently and optional are symmetric partners or themselves strengthened."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_46 : LinguisticExample :=
  { id := "brehenyetal2018_46"
    source := ⟨"breheny-et-al-2018", "(46)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John saw some of the students."
    discourseSegments := []
    glossedTokens := []
    translation := "John saw some of the students."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: John didn't see all of the students", .acceptable)]
    paperFeatures := [("case", "rsa"), ("prejacent", "some"), ("alternative", "all"), ("symmetric alternative", "just some")]
    comment := "The alternatives (47) include both all and just some; cost breaks the symmetry."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_48 : LinguisticExample :=
  { id := "brehenyetal2018_48"
    source := ⟨"breheny-et-al-2018", "(48)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John didn't see all of the students."
    discourseSegments := []
    glossedTokens := []
    translation := "John didn't see all of the students."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: John saw some of the students", .acceptable), ("inference, when many is relevant: John saw many of the students", .acceptable)]
    paperFeatures := [("case", "rsa"), ("prejacent", "not all"), ("alternative", "none"), ("symmetric alternative", "some")]
    comment := "The alternatives (49) tie in complexity; relative informativity breaks the symmetry. The second inference holds when whether John saw many of the students is relevant, with the alternatives (54)."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_50 : LinguisticExample :=
  { id := "brehenyetal2018_50"
    source := ⟨"breheny-et-al-2018", "(50)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The glass is not full."
    discourseSegments := []
    glossedTokens := []
    translation := "The glass is not full."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := [("inference: the glass is not empty", .acceptable)]
    paperFeatures := [("case", "rsa"), ("prejacent", "not full"), ("alternative", "not empty"), ("symmetric alternative", "empty")]
    comment := "With the alternatives (51), not empty is both less informative and costlier than empty."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_55 : LinguisticExample :=
  { id := "brehenyetal2018_55"
    source := ⟨"trinh-haida-2015", "(5)"⟩
    reportedIn := some ⟨"breheny-et-al-2018", "(55)"⟩
    language := "stan1293"
    primaryText := "John ran."
    discourseSegments := []
    glossedTokens := []
    translation := "John ran."
    context := "Bill ran and didn't smoke."
    judgment := .acceptable
    alternatives := []
    readings := [("inference: John smoked", .acceptable)]
    paperFeatures := [("case", "rsa"), ("prejacent", "run"), ("alternative", "run and not smoke"), ("symmetric alternative", "run and smoke")]
    comment := "The alternatives tie in informativity, and the unattested one is if anything simpler."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def ex_57 : LinguisticExample :=
  { id := "brehenyetal2018_57"
    source := ⟨"breheny-et-al-2018", "(57)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "The heater often squeaks."
    discourseSegments := []
    glossedTokens := []
    translation := "The heater often squeaks."
    context := ""
    judgment := .acceptable
    alternatives := []
    readings := []
    paperFeatures := [("case", "rsa"), ("prejacent", "often"), ("alternative", "always"), ("symmetric alternative", "intermittently")]
    comment := "With the alternatives (58), only a frequency cost on intermittently breaks the symmetry."
    metaLanguage := "stan1293"
    lgrConformance := "" }

def all : List LinguisticExample := [ex_1, ex_11, ex_12, ex_17, ex_18, ex_28, ex_32, ex_33, ex_34, ex_35, ex_38a, ex_38b, ex_38c, ex_41, ex_42a, ex_42b, ex_44, ex_45, ex_46, ex_48, ex_50, ex_55, ex_57]

end BrehenyEtAl2018.Examples
