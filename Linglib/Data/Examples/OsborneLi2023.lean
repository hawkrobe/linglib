import Linglib.Data.Examples.Schema

/-!
# `OsborneLi2023` — typed example data

Auto-generated from `Linglib/Data/Examples/OsborneLi2023.json` by
`scripts/gen_examples.py`. Do not edit by hand; edit the JSON and re-run
the generator. Consumers (the paper's study file, test-suite hubs) import
this module; declarations live in `namespace OsborneLi2023.Examples`.
-/

namespace OsborneLi2023.Examples

open Data.Examples

def ex2a : LinguisticExample :=
  { id := "osborneli2023_ex2a"
    source := ⟨"osborne-li-2023", "(2a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Max and Lucie talked about him."
    discourseSegments := []
    glossedTokens := []
    translation := "Max and Lucie talked about him."
    context := "Coordinate subject; pronoun in PP complement. CRDC predicts marginality of co-valuing `him` with `Max` (conjunct valent of the subject coordinate structure)."
    judgment := .questionable
    alternatives := []
    readings := [("him = Max (co-valued)", .questionable), ("him = external referent", .acceptable)]
    paperFeatures := [("coordinateSubject", "true"), ("coVValuedPair", "him;Max"), ("paperSection", "1"), ("paperMeanScore", "2.38"), ("paperNRespondents", "60")]
    comment := "Osborne & Li 2023 ex (2a), p. ~632. Crowdsourced mean 2.38 → `??` per paper p. 630 fn. 3 threshold table (1.65–2.29 = ?, 2.30–2.94 = ??, 2.95–4.00 = *)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex3a : LinguisticExample :=
  { id := "osborneli2023_ex3a"
    source := ⟨"osborne-li-2023", "(3a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John and Mary talked about himself."
    discourseSegments := []
    glossedTokens := []
    translation := "John and Mary talked about himself."
    context := "Coordinate subject; reflexive in PP complement. Co-valuing `himself` with `John` (a conjunct valent of the subject) is marginal — the reflexive cannot find a fully matching antecedent in the local domain but is licensed by the conjunct valent."
    judgment := .marginal
    alternatives := []
    readings := [("himself = John", .marginal)]
    paperFeatures := [("coordinateSubject", "true"), ("coVValuedPair", "himself;John"), ("anaphorType", "reflexive"), ("paperSection", "3"), ("paperMeanScore", "2.15"), ("paperNRespondents", "60")]
    comment := "Osborne & Li 2023 ex (3a). Mean 2.15 → `?` per threshold table. CRDC predicts marginality (full reflexive of conjunct antecedent); some speakers tolerate semantic-plural agreement, others not."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex3b : LinguisticExample :=
  { id := "osborneli2023_ex3b"
    source := ⟨"osborne-li-2023", "(3b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John and Mary talked about him."
    discourseSegments := []
    glossedTokens := []
    translation := "John and Mary talked about him."
    context := "Co-valuing `him` with `John` (conjunct valent of subject coordinate structure). Same CRDC structure as (2a) with masculine antecedent."
    judgment := .questionable
    alternatives := []
    readings := [("him = John (co-valued)", .questionable)]
    paperFeatures := [("coordinateSubject", "true"), ("coVValuedPair", "him;John"), ("paperSection", "3"), ("paperMeanScore", "2.43"), ("paperNRespondents", "60")]
    comment := "Osborne & Li 2023 ex (3b). Mean 2.43 → `??`."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex5a : LinguisticExample :=
  { id := "osborneli2023_ex5a"
    source := ⟨"osborne-li-2023", "(5a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Both John and Mary love him."
    discourseSegments := []
    glossedTokens := []
    translation := "Both John and Mary love him."
    context := "`both ... and ...` coordinator; pronoun as object of a symmetric predicate (`love`). Co-valuing `him` with `John` instantiates the CRDC configuration: `him` is a full valent, `John` is a conjunct of the coordinate subject."
    judgment := .questionable
    alternatives := []
    readings := [("him = John", .questionable)]
    paperFeatures := [("coordinateSubject", "true"), ("coordinator", "both...and"), ("coVValuedPair", "him;John"), ("paperSection", "3"), ("paperMeanScore", "UNVERIFIED"), ("paperNRespondents", "UNVERIFIED")]
    comment := "Osborne & Li 2023 ex (5a). CRDC predicts marginality (`.questionable`). Mean score and respondent count not verified against the paper PDF; the paired-coordinator variant pairs with a bare-`and` baseline that the paper itself uses to argue the symmetric-predicate `love` is the locus of the contrast, not the `both`-coordinator. Re-check both the score and the analytic attribution on next audit pass."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex6a : LinguisticExample :=
  { id := "osborneli2023_ex6a"
    source := ⟨"osborne-li-2023", "(6a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Bill and Mary consider him to be ready for a raise."
    discourseSegments := []
    glossedTokens := []
    translation := "Bill and Mary consider him to be ready for a raise."
    context := "Coordinate subject; pronoun in raising-to-object position. CRDC applies: `him` is a full valent of `consider` (raising-to-object); `Bill` is a conjunct valent of the coordinate subject. Co-valuation is marginal."
    judgment := .questionable
    alternatives := []
    readings := [("him = Bill", .questionable)]
    paperFeatures := [("coordinateSubject", "true"), ("construction", "raising-to-object"), ("coVValuedPair", "him;Bill"), ("paperSection", "3"), ("paperMeanScore", "2.42"), ("paperNRespondents", "60")]
    comment := "Osborne & Li 2023 ex (6a). Mean 2.42 → `??`. Raising-to-object case strengthens the empirical base for CRDC over coordinate-subject configurations."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex9a : LinguisticExample :=
  { id := "osborneli2023_ex9a"
    source := ⟨"osborne-li-2023", "(9a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Max talked about himself."
    discourseSegments := []
    glossedTokens := []
    translation := "Max talked about himself."
    context := "Non-coordinate baseline; reflexive licensed by Condition A. CRDC is silent (no coordination); the example is fully acceptable."
    judgment := .acceptable
    alternatives := []
    readings := [("himself = Max", .acceptable)]
    paperFeatures := [("coordinateSubject", "false"), ("coVValuedPair", "himself;Max"), ("paperSection", "3"), ("paperMeanScore", "1.28"), ("paperNRespondents", "60")]
    comment := "Osborne & Li 2023 ex (9a). Mean 1.28 → no indicator (acceptable). Non-coordinate baseline; CRDC says nothing because there is no coordination."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex9b : LinguisticExample :=
  { id := "osborneli2023_ex9b"
    source := ⟨"osborne-li-2023", "(9b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Max talked about him."
    discourseSegments := []
    glossedTokens := []
    translation := "Max talked about him."
    context := "Non-coordinate baseline; co-valuing `him` with local subject `Max` violates Condition B (not CRDC, which is silent here)."
    judgment := .questionable
    alternatives := []
    readings := [("him = Max", .questionable), ("him = external referent", .acceptable)]
    paperFeatures := [("coordinateSubject", "false"), ("coVValuedPair", "him;Max"), ("paperSection", "3"), ("paperMeanScore", "2.92"), ("paperNRespondents", "60")]
    comment := "Osborne & Li 2023 ex (9b). Mean 2.92 → `??`. The marginality here comes from Condition B (local pronoun bound by subject), not CRDC."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex11a : LinguisticExample :=
  { id := "osborneli2023_ex11a"
    source := ⟨"osborne-li-2023", "(11a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Max and Lucie talked about his work."
    discourseSegments := []
    glossedTokens := []
    translation := "Max and Lucie talked about his work."
    context := "Coordinate subject; possessive pronoun inside object PP. Possessives embed the conjunct-valent referent inside a further DP, weakening CRDC's marginality prediction."
    judgment := .acceptable
    alternatives := []
    readings := [("his = Max", .acceptable)]
    paperFeatures := [("coordinateSubject", "true"), ("coVValuedPair", "his;Max"), ("anaphorType", "possessive"), ("paperSection", "3"), ("paperMeanScore", "1.20"), ("paperNRespondents", "60")]
    comment := "Osborne & Li 2023 ex (11a). Mean 1.20 → no indicator. Embedding the pronoun inside a possessive DP defuses CRDC."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex11e : LinguisticExample :=
  { id := "osborneli2023_ex11e"
    source := ⟨"osborne-li-2023", "(11e)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Max and Lucie talked about Max."
    discourseSegments := []
    glossedTokens := []
    translation := "Max and Lucie talked about Max."
    context := "Coordinate subject; R-expression repeated as object. Condition C is in play, not CRDC. The repeated R-expression is acceptable on the disjoint reading (two different Maxes)."
    judgment := .acceptable
    alternatives := []
    readings := [("object Max ≠ subject Max", .acceptable), ("object Max = subject Max (same individual)", .marginal)]
    paperFeatures := [("coordinateSubject", "true"), ("coVValuedPair", "Max;Max"), ("anaphorType", "R-expression"), ("paperSection", "3"), ("paperMeanScore", "1.47"), ("paperNRespondents", "100")]
    comment := "Osborne & Li 2023 ex (11e). Mean 1.47 → no indicator. R-expressions skirt CRDC because they need no antecedent."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex20b : LinguisticExample :=
  { id := "osborneli2023_ex20b"
    source := ⟨"osborne-li-2023", "(20b)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Hank and Hillary appear to her to be good friends."
    discourseSegments := []
    glossedTokens := []
    translation := "Hank and Hillary appear to her to be good friends."
    context := "Subject-to-subject raising over an experiencer PP. `her` is a full valent of `appear`; `Hillary` is a conjunct valent of the raised subject coordinate structure. CRDC predicts marginality of co-valuation."
    judgment := .questionable
    alternatives := []
    readings := [("her = Hillary", .questionable)]
    paperFeatures := [("coordinateSubject", "true"), ("construction", "raising-with-experiencer"), ("coVValuedPair", "her;Hillary"), ("paperSection", "3"), ("paperMeanScore", "2.68"), ("paperNRespondents", "60")]
    comment := "Osborne & Li 2023 ex (20b). Mean 2.68 → `??`. Raising-with-experiencer pattern: CRDC continues to apply across the raising chain."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex24a : LinguisticExample :=
  { id := "osborneli2023_ex24a"
    source := ⟨"osborne-li-2023", "(24a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John talked about himself and his mother."
    discourseSegments := []
    glossedTokens := []
    translation := "John talked about himself and his mother."
    context := "Coordinate *object*, not coordinate subject. `himself` is a conjunct valent of a full valent of `talked`; co-valuation with the full-valent subject `John` is the reverse direction of CRDC (conjunct anaphor of full antecedent), which CRDC explicitly permits."
    judgment := .acceptable
    alternatives := []
    readings := [("himself = John", .acceptable)]
    paperFeatures := [("coordinateObject", "true"), ("coVValuedPair", "himself;John"), ("paperSection", "3"), ("paperMeanScore", "1.14"), ("paperNRespondents", "60")]
    comment := "Osborne & Li 2023 ex (24a). Mean 1.14 → no indicator. Key directionality test: conjunct anaphor of full-valent antecedent is fine; only the full-anaphor-of-conjunct direction triggers CRDC marginality."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex25c : LinguisticExample :=
  { id := "osborneli2023_ex25c"
    source := ⟨"osborne-li-2023", "(25c)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Jane defended her."
    discourseSegments := []
    glossedTokens := []
    translation := "Jane defended her."
    context := "Non-coordinate Condition B violation. Co-valuing `her` with local subject `Jane` is straightforwardly ungrammatical. CRDC is silent (no coordination)."
    judgment := .ungrammatical
    alternatives := []
    readings := [("her = Jane", .ungrammatical)]
    paperFeatures := [("coordinateSubject", "false"), ("coVValuedPair", "her;Jane"), ("paperSection", "3"), ("paperMeanScore", "3.20"), ("paperNRespondents", "40")]
    comment := "Osborne & Li 2023 ex (25c). Mean 3.20 → `*`. Standard Condition B violation; cited to contrast with the coordinate-object licensing in (24a)."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex28d : LinguisticExample :=
  { id := "osborneli2023_ex28d"
    source := ⟨"osborne-li-2023", "(28d)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "John expected Mary and him to be able to leave soon."
    discourseSegments := []
    glossedTokens := []
    translation := "John expected Mary and him to be able to leave soon."
    context := "Raising-to-object with coordinate object; `him` is a conjunct valent of the embedded subject. Co-valuing `him` with matrix-subject `John` (a full valent of `expected`) is acceptable — the reverse CRDC direction (conjunct anaphor of full antecedent)."
    judgment := .acceptable
    alternatives := []
    readings := [("him = John", .acceptable)]
    paperFeatures := [("coordinateObject", "true"), ("construction", "raising-to-object"), ("coVValuedPair", "him;John"), ("paperSection", "3"), ("paperMeanScore", "1.40"), ("paperNRespondents", "60")]
    comment := "Osborne & Li 2023 ex (28d). Mean 1.40 → no indicator. Confirms the directionality asymmetry: conjunct anaphor of full antecedent is fine even with raising-to-object."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def ex55a : LinguisticExample :=
  { id := "osborneli2023_ex55a"
    source := ⟨"osborne-li-2023", "(55a)"⟩
    reportedIn := none
    language := "stan1293"
    primaryText := "Sophy and Edgar voted for her."
    discourseSegments := []
    glossedTokens := []
    translation := "Sophy and Edgar voted for her."
    context := "Coordinate-subject CRDC configuration, but a structural counterexample: speakers accept co-valuation of `her` with `Sophy` despite CRDC's marginality prediction. Paper discusses this as a candidate exception (Section 6)."
    judgment := .acceptable
    alternatives := []
    readings := [("her = Sophy", .acceptable)]
    paperFeatures := [("coordinateSubject", "true"), ("coVValuedPair", "her;Sophy"), ("paperSection", "6"), ("isCounterexample", "true"), ("paperMeanScore", "1.43"), ("paperNRespondents", "40")]
    comment := "Osborne & Li 2023 ex (55a). Mean 1.43 → no indicator. Section 6 counterexample: predicates like `vote for` allow `her` to pick out an individual outside the coordination (a third party), making CRDC's prediction empirically wrong here. Flagged in `paperFeatures.isCounterexample`."
    metaLanguage := "stan1293"
    lgrConformance := "WORD_ALIGNED" }

def all : List LinguisticExample := [ex2a, ex3a, ex3b, ex5a, ex6a, ex9a, ex9b, ex11a, ex11e, ex20b, ex24a, ex25c, ex28d, ex55a]

end OsborneLi2023.Examples
