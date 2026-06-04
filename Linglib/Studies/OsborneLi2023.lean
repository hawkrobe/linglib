import Linglib.Syntax.DependencyGrammar.Basic
import Linglib.Core.UD.Word
import Linglib.Data.Examples.Schema
import Linglib.Syntax.DependencyGrammar.Coordination

/-!
# CRDC: Conjunct Referential Dependency Constraint
[osborne-li-2023]

The Conjunct Referential Dependency Constraint (CRDC), formulated by
[osborne-li-2023] in *Folia Linguistica* 57(3): 629–659, is a
dependency-grammar constraint on co-valuation in sentences that involve
coordinate structures.

Paper text, p. 651 (verbatim):

> A referentially dependent conjunct valent can be co-valued with a full
> co-valent, but a referentially dependent full valent can hardly be
> co-valued with a conjunct co-valent.

The CRDC governs *only* configurations in which one of the relevant
positions sits inside a coordinate structure; non-coordinate binding
falls under standard binding-theoretic principles (Conditions A/B/C).
The paper is explicit on p. 651: "The CRDC therefore says nothing about
[cases where no coordination is involved]."

Marginality is constitutive of the CRDC's empirical content. The paper's
crowdsourced acceptability table (p. 630 fn. 3) maps mean scores to
markers — `?` (1.65–2.29), `??` (2.30–2.94), `*` (2.95–4.00). The CRDC's
prediction is `??`, which corresponds to `Judgment.questionable` in the
project's 5-level enum.

## Main definitions

* `isConjunctValent` / `isFullValent` — the paper's predicate-valent
  type distinction, operationalised over `DepTree` via
  `UD.DepRel.isValencyArg` from `Core/UD.lean`.
* `crdcPredictedJudgment` — the `Judgment` the CRDC assigns to a
  candidate co-valuation; `.questionable` exactly when CRDC fires,
  `.acceptable` when CRDC is silent (other binding principles may
  still apply).

## Implementation notes

* "Valent" is operationalised as a direct UD valency-relation dependent
  of the predicate. This is a deliberate simplification of the paper's
  catena-based notion (paper §4); the example set does not exercise the
  distinction.
* `getConjuncts` is reused from `DepGrammar.Coordination` rather than
  reinventing coord-structure traversal. UD's basic-tree convention
  makes the first conjunct the head of the coordinate structure; the
  remaining conjuncts attach via `.conj`.
* The CRDC alone is not a full binding theory — it predicts only the
  coord-conjunct-vs-full-valent contribution to acceptability. Example
  (9b) "Max talked about him" is sentence-level `.questionable` from
  Condition B, but `crdcPredictedJudgment` returns `.acceptable`
  because the CRDC is silent on non-coordinate cases.

## Cross-framework relationship

The standard binding theories formalized elsewhere in linglib —
[chomsky-1981] (`Studies/Chomsky1981.lean`),
[hudson-1990] (`Studies/Hudson1990.lean`),
[pollard-sag-1994] / [sag-wasow-bender-2003]
(`Syntax/HPSG/Coreference.lean`,
`Studies/SagWasowBender2003.lean`) — make *categorical*
predictions via `Bool`-valued `grammaticalForCoreference`. The CRDC
contributes a *graded* prediction (`.questionable`) that those
predicates cannot express in their current shape; the comparison is
not a head-to-head bake-off because the two frameworks answer
different questions on disjoint stimulus subsets:

* CRDC: graded marginality, coordinate-structure stimuli, silent
  on non-coordinate cases (paper p. 651 explicit).
* Conditions A/B/C: categorical grammaticality, non-coordinate
  stimuli (current parsers do not traverse coordinate structures,
  so any coordinated input categorically returns `false` — a
  parser limitation, not a theoretical claim).

A direct CRDC-vs-Conditions-A/B/C bake-off requires (a) extending
the binding-theory parsers to coordination and (b) lifting their
output to `Judgment`. Both are out of scope for this study file.

## Todo

* Paper §6 counterexamples (e.g. *vote*-predicate identity split,
  example (55a) in the JSON) are encoded as data but not yet covered
  by a CRDC-vs-data theorem; needs integration with a third-party-
  referent disjunct.
* Paper §7 — coordination-as-phrase-structure vs subordination-as-
  dependency contrast — is theoretical commentary without formal
  content here yet.
* Bool→Prop migration of `isConjunctValent` / `isFullValent` should
  happen as part of a unified `DepGrammar/*` sweep, not piecemeal.
* Cross-framework CRDC-vs-Conditions-A/B/C bake-off blocked on
  parser/coordination work (see Cross-framework relationship).
-/

namespace OsborneLi2023

open DepGrammar
open DepGrammar.Coordination
open Data.Examples (LinguisticExample)
open Paradigms.AcceptabilityJudgment (Judgment)

/-! ### Predicate-valent type -/

/-- Word `valentIdx` is a *conjunct valent* of predicate `predIdx`: it
    is a conjunct of a coordinate structure that fills a valency role
    of `predIdx`. Concretely: there is a valency-eligible edge from
    `predIdx` to some coord-head `c`, and `valentIdx` is in
    `allConjuncts c` (the first conjunct, which heads the structure
    in UD, plus the remaining conjuncts attached via `.conj`). -/
def isConjunctValent (t : DepTree) (predIdx valentIdx : Nat) : Bool :=
  t.deps.any λ d =>
    d.headIdx == predIdx && d.depType.isValencyArg
      && hasConjuncts t d.depIdx
      && (allConjuncts t d.depIdx).contains valentIdx

/-- Word `valentIdx` is a *full valent* of `predIdx`: a valent of
    `predIdx` that is not a conjunct valent. Matches the paper's
    definition (p. 651): "a valent of a given predicate is a full
    valent thereof if it is complete, that is, it is *not* a conjunct
    valent." Operationalised as "direct valency-eligible dependent of
    `predIdx` AND not a conjunct valent." -/
def isFullValent (t : DepTree) (predIdx valentIdx : Nat) : Bool :=
  (t.deps.any λ d =>
      d.headIdx == predIdx && d.depType.isValencyArg
        && d.depIdx == valentIdx)
    && ¬ isConjunctValent t predIdx valentIdx

/-! ### CRDC prediction -/

/-- The CRDC's predicted judgment for co-valuing anaphor `anaIdx` with
    antecedent `anteIdx` under predicate `predIdx` in tree `t`.

    Fires (`.questionable`) exactly when the anaphor is a full valent
    and the antecedent is a conjunct valent of the same predicate.
    Otherwise returns `.acceptable` — CRDC is silent, and other binding
    principles (Conditions A/B/C) may still apply. -/
def crdcPredictedJudgment
    (t : DepTree) (predIdx anaIdx anteIdx : Nat) : Judgment :=
  if isFullValent t predIdx anaIdx && isConjunctValent t predIdx anteIdx then
    .questionable
  else
    .acceptable

-- BEGIN GENERATED EXAMPLES
-- (Generated from Linglib/Data/Examples/OsborneLi2023.json by scripts/gen_examples.py.
-- Do not edit between markers; re-run the generator after editing the JSON.)

namespace Examples
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

end Examples
-- END GENERATED EXAMPLES

/-! ### CRDC-prediction theorems

Each theorem builds a `DepTree` matching one of the example sentences
and checks that `crdcPredictedJudgment` returns the contribution the
CRDC is responsible for. For data points whose sentence-level judgment
is set by a different principle (e.g. ex9b by Condition B, ex5a
strengthened by `both...and`), the theorem records that CRDC alone
predicts `.acceptable` or `.questionable` respectively — separating the
CRDC's contribution from other determinants of acceptability. -/

/-- Tree for "Max and Lucie talked about him."
    `Max(0) and(1) Lucie(2) talked(3) about(4) him(5)`. -/
def ex2a_tree : DepTree :=
  { words := [ { form :="Max", cat := .PROPN, features := {}}, { form :="and", cat := .CCONJ, features := {}}
             , { form :="Lucie", cat := .PROPN, features := {}}, { form :="talked", cat := .VERB, features := {}}
             , { form :="about", cat := .ADP, features := {}}, { form :="him", cat := .PRON, features := {}} ]
    deps  := [ ⟨3, 0, .nsubj⟩, ⟨0, 1, .cc⟩, ⟨0, 2, .conj⟩
             , ⟨3, 5, .obl⟩, ⟨5, 4, .case_⟩ ]
    rootIdx := 3 }

theorem ex2a_predicts_questionable :
    crdcPredictedJudgment ex2a_tree 3 5 0 = .questionable := by decide

/-- Tree for "Max talked about himself." — non-coordinate baseline. -/
def ex9a_tree : DepTree :=
  { words := [ { form :="Max", cat := .PROPN, features := {}}, { form :="talked", cat := .VERB, features := {}}
             , { form :="about", cat := .ADP, features := {}}, { form :="himself", cat := .PRON, features := {}} ]
    deps  := [ ⟨1, 0, .nsubj⟩, ⟨1, 3, .obl⟩, ⟨3, 2, .case_⟩ ]
    rootIdx := 1 }

theorem ex9a_predicts_acceptable :
    crdcPredictedJudgment ex9a_tree 1 3 0 = .acceptable := by decide

/-- Tree for "Max talked about him." — non-coordinate Condition B
    context. The sentence-level `.questionable` reading comes from
    Condition B, not the CRDC; here we record only that the CRDC is
    silent. -/
def ex9b_tree : DepTree :=
  { words := [ { form :="Max", cat := .PROPN, features := {}}, { form :="talked", cat := .VERB, features := {}}
             , { form :="about", cat := .ADP, features := {}}, { form :="him", cat := .PRON, features := {}} ]
    deps  := [ ⟨1, 0, .nsubj⟩, ⟨1, 3, .obl⟩, ⟨3, 2, .case_⟩ ]
    rootIdx := 1 }

theorem ex9b_crdc_silent :
    crdcPredictedJudgment ex9b_tree 1 3 0 = .acceptable := by decide

/-- Tree for "John talked about himself and his mother." — coordinate
    *object*. `himself` heads the coord, so it is a conjunct valent;
    `John` is a full valent. CRDC's permitted direction (conjunct
    anaphor of full antecedent). -/
def ex24a_tree : DepTree :=
  { words := [ { form :="John", cat := .PROPN, features := {}}, { form :="talked", cat := .VERB, features := {}}
             , { form :="about", cat := .ADP, features := {}}, { form :="himself", cat := .PRON, features := {}}
             , { form :="and", cat := .CCONJ, features := {}}, { form :="his", cat := .PRON, features := {}}
             , { form :="mother", cat := .NOUN, features := {}} ]
    deps  := [ ⟨1, 0, .nsubj⟩, ⟨1, 3, .obl⟩, ⟨3, 2, .case_⟩
             , ⟨3, 4, .cc⟩, ⟨3, 6, .conj⟩, ⟨6, 5, .nmod⟩ ]
    rootIdx := 1 }

theorem ex24a_predicts_acceptable :
    crdcPredictedJudgment ex24a_tree 1 3 0 = .acceptable := by decide

/-- Tree for "Both John and Mary love him." — coordinate subject with
    paired coordinator; pronoun in object position. The CRDC fires.
    Sentence-level judgment is stronger (`.ungrammatical`) due to
    `both...and` strengthening; the CRDC alone predicts
    `.questionable`. -/
def ex5a_tree : DepTree :=
  { words := [ { form :="Both", cat := .CCONJ, features := {}}, { form :="John", cat := .PROPN, features := {}}
             , { form :="and", cat := .CCONJ, features := {}}, { form :="Mary", cat := .PROPN, features := {}}
             , { form :="love", cat := .VERB, features := {}}, { form :="him", cat := .PRON, features := {}} ]
    deps  := [ ⟨4, 1, .nsubj⟩, ⟨1, 0, .cc⟩, ⟨1, 2, .cc⟩
             , ⟨1, 3, .conj⟩, ⟨4, 5, .obj⟩ ]
    rootIdx := 4 }

theorem ex5a_predicts_questionable :
    crdcPredictedJudgment ex5a_tree 4 5 1 = .questionable := by decide

/-- Tree for "John expected Mary and him to be able to leave soon."
    Coordinate-*object* under raising-to-object; `John` is the matrix
    subject (full valent), `him` is a conjunct of the embedded subject
    coord. Permitted direction; the CRDC is silent on `him↔John`
    co-valuation because `him` is a conjunct valent (not a full valent). -/
def ex28d_tree : DepTree :=
  { words := [ { form :="John", cat := .PROPN, features := {}}, { form :="expected", cat := .VERB, features := {}}
             , { form :="Mary", cat := .PROPN, features := {}}, { form :="and", cat := .CCONJ, features := {}}
             , { form :="him", cat := .PRON, features := {}}, { form :="to", cat := .PART, features := {}}
             , { form :="leave", cat := .VERB, features := {}}, { form :="soon", cat := .ADV, features := {}} ]
    deps  := [ ⟨1, 0, .nsubj⟩, ⟨1, 2, .obj⟩, ⟨2, 3, .cc⟩
             , ⟨2, 4, .conj⟩, ⟨1, 6, .xcomp⟩, ⟨6, 5, .mark⟩
             , ⟨6, 7, .advmod⟩ ]
    rootIdx := 1 }

theorem ex28d_predicts_acceptable :
    crdcPredictedJudgment ex28d_tree 1 4 0 = .acceptable := by decide

/-! ### Directionality

The CRDC is asymmetric: full-anaphor-of-conjunct-antecedent triggers
marginality (`.questionable`); the reverse direction (conjunct-anaphor
of-full-antecedent) does not. The asymmetry is exhibited on a single
tree by swapping `anaIdx` and `anteIdx`: only the (full, conjunct)
ordering fires the constraint. -/

/-- On ex2a's tree, swapping which index is the anaphor and which is
    the antecedent flips the verdict — only `him` (full) over `Max`
    (conjunct) triggers the CRDC. The reverse swap is structurally
    irreflexive of CRDC's prediction function; it does not correspond
    to a semantically coherent anaphoric reading. -/
theorem direction_asymmetry :
    -- (a) Blocked direction: full anaphor of conjunct antecedent
    crdcPredictedJudgment ex2a_tree 3 5 0 = .questionable ∧
    -- (b) Permitted direction (same tree, swapped indices)
    crdcPredictedJudgment ex2a_tree 3 0 5 = .acceptable := by
  refine ⟨?_, ?_⟩ <;> decide

end OsborneLi2023
