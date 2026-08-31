import Linglib.Studies.BhattPancheva2004
import Linglib.Studies.Lechner2004
import Linglib.Syntax.Minimalist.Movement.DegreeMovement

/-!
# Bhatt and Takahashi 2011: reduced and unreduced phrasal comparatives

This file formalizes the diagnostics of [bhatt-takahashi-2011] for the two analyses of a phrasal
comparative: reduction of a clausal source, using the two-place degree head, or a genuinely phrasal
standard combining with an individual, using the three-place head. The binding generalization of §2
— the standard is c-commanded by everything that c-commands the associate — holds in English,
which is the signature of reduction and reverses the verdict of [bhatt-pancheva-2004]; Hindi-Urdu
fails it, since the standard is an external PP. §4's scope generalization sorts the two languages
the same way. Each language's realized analyses are therefore read off its data rather than
stipulated, and §6 proposes that both degree heads are universally available, their distribution
fixed by the subcategorization of *than*, *yori* and *-se*.

The binding schema (`BindingDatum`, `realizesReduction`, `realizesDirect`,
`headAvailabilityFromBinding`) is [lechner-2004]'s disjoint-reference battery, on which the paper
models its English examples (fn. 4); it lives in `Studies/Lechner2004.lean`.

Out of scope: the Single Standard Restriction (§3.2) and the Precedence Constraint (§3.3), which
need an overt linear-order interface; the derivation of Japanese's realized analyses from *yori*'s
subcategorization (§5–§6), which is stipulated here.

## Main definitions

* `englishBindingPairs`, `hindiUrduBindingPairs` — the §2 and §3.4 minimal pairs
* `englishScopeData`, `hindiUrduScopeData`, `scopeRealizesReduction` — the §4 scope diagnostic
* `englishHeadAvailability`, `hindiUrduHeadAvailability` — realized analyses, derived from the data

## Main results

* `english_data_realizes_reduction`, `english_data_rules_out_direct` — English binding is the
  reduction pattern
* `hindi_urdu_data_realizes_direct`, `hindi_urdu_data_rules_out_reduction` — Hindi-Urdu is not
* `english_scope_matches_RA`, `hindi_urdu_scope_rules_out_RA` — the scope diagnostic agrees
* `bt2011_verdict_matches_data_bp2004_verdict_does_not` — the disagreement with
  [bhatt-pancheva-2004] is empirical, not terminological
* `bt2011_agrees_with_bresnan_against_bp2004` — the reduction verdict re-vindicates [bresnan-1973]
* `surveyed_languages_pairwise_distinct` — the surveyed languages occupy three cells of the grid

## References

* [bhatt-takahashi-2011]
* [bhatt-pancheva-2004]
* [lechner-2004]
* [bresnan-1973]
-/

namespace BhattTakahashi2011

open Lechner2004 (BindingDatum RAPredictsCoref DAPredictsCoref
  realizesReduction realizesDirect HeadAvailability headAvailabilityFromBinding
  PhrasalAnalysis)
open Bresnan1973 (BresnanThanClauseAnalysis bresnanAnalysisOf)
open Features (Acceptability)
open Minimalist.DegreeMovement
  (ScopeBinding IsBhattTakahashiScopeLicit
   not_isBhattTakahashiScopeLicit_base_above_DegP
   isBhattTakahashiScopeLicit_base_below_DegP)

-- ════════════════════════════════════════════════════
-- § 1. The two-analyses framework (B&T §1)
-- ════════════════════════════════════════════════════

-- B&T's analytic vocabulary is Lechner's: the two analyses of phrasal
-- comparatives — RA (.reduction) and DA (.direct) — live in
-- `Lechner2004.PhrasalAnalysis`.

-- ════════════════════════════════════════════════════
-- § 2. English binding diagnostic (B&T §2, generalization (10))
-- ════════════════════════════════════════════════════

/-- The English minimal pairs (11)–(13), modelled by the paper on [lechner-2004] (fn. 4). Each
pair contrasts a pronoun that c-commands the associate, where coreference into the standard is
blocked, with one that does not, where it is licit. (13b) is marginal for some speakers (fn. 5),
which is still the coreference-licit direction. -/
def englishBindingPairs : List BindingDatum :=
  [-- (11a) *More people introduced himᵢ to Mary than to Johnᵢ's mother.
   { citationId := "11a", acceptability := .unacceptable
     pronCCommandsAssociate := true,  corefAttested := false },
   -- (11b) Mary introduced himᵢ to more people than Johnᵢ's mother.
   { citationId := "11b", acceptability := .ok
     pronCCommandsAssociate := false, corefAttested := true },
   -- (12a) *More people talked to himᵢ about Sally than about Peterᵢ's sister.
   { citationId := "12a", acceptability := .unacceptable
     pronCCommandsAssociate := true,  corefAttested := false },
   -- (12b) More people talked to Sally about himᵢ than to Peterᵢ's sister.
   { citationId := "12b", acceptability := .ok
     pronCCommandsAssociate := false, corefAttested := true },
   -- (13a) *More people expect himᵢ to overtake Sally than Peterᵢ's sister.
   { citationId := "13a", acceptability := .unacceptable
     pronCCommandsAssociate := true,  corefAttested := false },
   -- (13b) (?)More people expect Sally to overtake himᵢ than Peterᵢ's sister.
   { citationId := "13b", acceptability := .marginal
     pronCCommandsAssociate := false, corefAttested := true }]

/-- B&T (10), formalized: the English data is consistent with RA on
    every minimal pair. Coreference is grammatical iff the matrix
    pronoun does not c-command the associate. -/
theorem english_data_realizes_reduction :
    realizesReduction englishBindingPairs := by
  decide

/-- The Direct Analysis predicts uniform coreference availability,
    contradicted by the c-command-blocks-coref data points (11a),
    (12a), (13a). DA cannot be the analysis at work in English. -/
theorem english_data_rules_out_direct :
    ¬ realizesDirect englishBindingPairs := by
  decide

-- ════════════════════════════════════════════════════
-- § 3. Hindi-Urdu binding diagnostic (B&T §3.4, datum (35))
-- ════════════════════════════════════════════════════

/-- B&T §3.4 Hindi-Urdu data. The standard's binding properties are
    independent of the associate's: even when the matrix pronoun
    c-commands the associate (because it precedes the standard in the
    head-final word order), coreference with an R-expression in the
    standard is grammatical, because the standard is an external PP
    that the matrix pronoun never c-commands.

(35) supplies the coreference-with-c-command example — *Atif showed Mohan's sister's picture to
    himᵢ more times than Raviᵢ's sister's picture* — and the second entry is the no-c-command
    baseline. -/
def hindiUrduBindingPairs : List BindingDatum :=
  [-- B&T (35): pronoun c-commands associate, coref STILL licit
   { citationId := "35", acceptability := .ok
     pronCCommandsAssociate := true,  corefAttested := true },
   -- (35-control): no-c-command baseline
   { citationId := "35-ctrl", acceptability := .ok
     pronCCommandsAssociate := false, corefAttested := true }]

/-- B&T §3.4: Hindi-Urdu data is consistent with DA. The key data
    point is (35), where coreference is grammatical even though the
    matrix pronoun c-commands the associate. -/
theorem hindi_urdu_data_realizes_direct :
    realizesDirect hindiUrduBindingPairs := by
  decide

/-- Hindi-Urdu data rules out RA: at the (35) data point, RA predicts
    no coreference (matrix pronoun c-commands the associate, hence
    c-commands the standard's R-expression), but coreference is in
    fact attested. -/
theorem hindi_urdu_data_rules_out_reduction :
    ¬ realizesReduction hindiUrduBindingPairs := by
  decide

-- ════════════════════════════════════════════════════
-- § 4. The walked-back B&P 2004 claim
-- ════════════════════════════════════════════════════

/-- B&T 2011's verdict for English (§2): only the Reduction Analysis
    is available. -/
def englishAnalysisPerBhattTakahashi2011 : PhrasalAnalysis := .reduction

/-- [bhatt-pancheva-2004] §1.1.1 fn. 4's verdict for English,
    restated in B&T's vocabulary: phrasal "than NP" is genuinely
    phrasal (DA), not a reduction of clausal "than [NP is Adj]". -/
def englishAnalysisPerBhattPancheva2004 : PhrasalAnalysis := .direct

/-- The two papers genuinely disagree about English. -/
theorem bp2004_bt2011_disagree_about_english :
    englishAnalysisPerBhattPancheva2004 ≠ englishAnalysisPerBhattTakahashi2011 := by
  decide

/-- The empirical content of the disagreement: B&T's verdict for
    English (RA) is the analysis whose predictions match the §2 data;
    B&P's verdict (DA) makes the wrong prediction at the
    c-command-blocks-coref data points. -/
theorem bt2011_verdict_matches_data_bp2004_verdict_does_not :
    realizesReduction englishBindingPairs ∧ ¬ realizesDirect englishBindingPairs :=
  ⟨english_data_realizes_reduction, english_data_rules_out_direct⟩

-- ════════════════════════════════════════════════════
-- § 4b. Scope generalization (B&T §4, eq. (43))
-- ════════════════════════════════════════════════════

/-- A B&T §4 scope datum: a `ScopeBinding` paired with an
    observational record of whether than-internal scope is attested
    for the configuration. The `qpBasePosition` field of the binding
    is what (43) keys on (not the surface-scope `qpHeight`). -/
structure ScopeDatum where
  citationId : String
  binding : ScopeBinding
  thanInternalScopeAttested : Bool
  deriving Repr

/-- The English scope data of (43): a quantifier inside the 'than'-phrase must scope out when its
base position c-commands the than-phrase-internal degree trace, and may otherwise take scope
within the 'than'-phrase. -/
def englishScopeData : List ScopeDatum :=
  [-- (43b) Craige assigned more students every paper by Hellan than every paper by …:
   -- base does not c-command the degree trace, than-internal scope licit
   { citationId := "43b"
     binding := ⟨1, 1, 1, false⟩
     thanInternalScopeAttested := true },
   -- (43a) Craige assigned every first year student more papers than every second year student:
   -- base c-commands the degree trace, the quantifier must scope out
   { citationId := "43a"
     binding := ⟨1, 2, 2, true⟩
     thanInternalScopeAttested := false }]

/-- B&T §4 (43) Hindi-Urdu scope data. RA predicts than-internal
    scope should be available for low-base QPs, but Hindi-Urdu
    *forces* scope-out: than-internal scope is unattested even when
    the base position is at or below the DegP.

The datum records §4.2's verdict that Hindi-Urdu scopes
    out obligatorily. -/
def hindiUrduScopeData : List ScopeDatum :=
  [-- low-base existential: RA would predict than-internal scope, but
   -- Hindi-Urdu does not allow it (scope-out is obligatory)
   { citationId := "HU-low"
     binding := ⟨1, 1, 1, false⟩
     thanInternalScopeAttested := false }]

/-- RA's prediction for a single scope datum: than-internal scope is
    attested iff the QP's base position is at or below the DegP. -/
def RAPredictsThanInternalScope (d : ScopeDatum) : Prop :=
  IsBhattTakahashiScopeLicit d.binding ↔ d.thanInternalScopeAttested = true

instance (d : ScopeDatum) : Decidable (RAPredictsThanInternalScope d) := by
  unfold RAPredictsThanInternalScope; infer_instance

/-- A language's scope data *realizes* RA iff every datum matches the
    B&T (43) biconditional prediction. -/
def scopeRealizesReduction (data : List ScopeDatum) : Prop :=
  ∀ d ∈ data, RAPredictsThanInternalScope d

instance (data : List ScopeDatum) : Decidable (scopeRealizesReduction data) := by
  unfold scopeRealizesReduction; exact List.decidableBAll _ _

/-- Parallel to `english_data_realizes_reduction` for the binding
    diagnostic: English scope data also matches RA. -/
theorem english_scope_matches_RA :
    scopeRealizesReduction englishScopeData := by
  decide

/-- Parallel to `hindi_urdu_data_rules_out_reduction`: Hindi-Urdu
    scope data also rules out RA. The low-base configuration would
    license than-internal scope under RA, but Hindi-Urdu data shows
    scope-out is obligatory. -/
theorem hindi_urdu_scope_rules_out_RA :
    ¬ scopeRealizesReduction hindiUrduScopeData := by
  decide

-- ════════════════════════════════════════════════════
-- § 5. Cross-tradition bridge to Bresnan 1973
-- ════════════════════════════════════════════════════

/-- B&T's `reduction` and Bresnan's `partialDeletion`/`maximalDeletion`
    are the same kind of analysis: surface forms derive from underlying
    clausal sources via syntactic deletion. -/
def isReductionStyleBT : PhrasalAnalysis → Bool
  | .reduction => true
  | .direct    => false

/-- Bresnan's two clausal-source pathways are both "reduction-style"
    in B&T's vocabulary: both posit a clausal underlying structure
    that is reduced by deletion to surface form. -/
def isReductionStyleBresnan : BresnanThanClauseAnalysis → Bool
  | .partialDeletion => true
  | .maximalDeletion => true

/-- Cross-tradition bridge: B&T 2011's verdict for English (RA)
    re-vindicates [bresnan-1973]'s analysis of English phrasal
    comparatives (`maximalDeletion`) against
    [bhatt-pancheva-2004]'s direct analysis. The agreement is at
    the level of analytic style — both posit a clausal source for
    surface phrasal "than NP", differing only in vocabulary. -/
theorem bt2011_agrees_with_bresnan_against_bp2004 :
    isReductionStyleBT englishAnalysisPerBhattTakahashi2011 = true ∧
    isReductionStyleBresnan (bresnanAnalysisOf .phrasal) = true ∧
    isReductionStyleBT englishAnalysisPerBhattPancheva2004 = false := by
  decide

-- ════════════════════════════════════════════════════
-- § 6. The typology proposal (B&T §6, eq. (63))
-- ════════════════════════════════════════════════════

/-- English (B&T §2): head-availability *derived* from the §2 binding
    data. RA is consistent with the data; DA is ruled out. -/
def englishHeadAvailability : HeadAvailability :=
  headAvailabilityFromBinding englishBindingPairs

/-- Hindi-Urdu (B&T §3): head-availability *derived* from the §3.4
    binding data. DA is consistent with the data; RA is ruled out. -/
def hindiUrduHeadAvailability : HeadAvailability :=
  headAvailabilityFromBinding hindiUrduBindingPairs

/-- Anti-stipulation witness for English: the derived head-availability
    is `⟨true, false⟩` (RA realized, DA not realized). The Bool
    values are *computed* from the data; this theorem just exposes
    them so downstream code can read them off. -/
theorem english_head_availability_derived :
    englishHeadAvailability = ⟨true, false⟩ := by
  decide

/-- Anti-stipulation witness for Hindi-Urdu: the derived
    head-availability is `⟨false, true⟩` (RA ruled out, DA
    realized). -/
theorem hindi_urdu_head_availability_derived :
    hindiUrduHeadAvailability = ⟨false, true⟩ := by
  decide

/-- Japanese realizes both: a clausal or multiple-standard complement of *yori* forces the 2-place
head, while a DP complement is analysed as a DP and takes the 3-place head (§6). Unlike English and
Hindi-Urdu this is stipulated rather than derived, since the argument runs through *yori*'s
subcategorization and the multiple-standard diagnostics of §5. -/
def japaneseHeadAvailability : HeadAvailability := ⟨true, true⟩

/-- B&T's surveyed languages, in citation order. The list is the unit
    of cross-linguistic generalization; per-pair distinctness theorems
    are derived over its elements. -/
def surveyedLanguages : List (String × HeadAvailability) :=
  [("English",    englishHeadAvailability),
   ("Hindi-Urdu", hindiUrduHeadAvailability),
   ("Japanese",   japaneseHeadAvailability)]

/-- B&T (63a) restated as a surveyed-language fact: every surveyed
    language realizes at least one of the two analyses. (B&T's
    stronger universal claim — that no language *lacks* either
    underlying head — is not directly observable from binding data
    alone.) -/
theorem all_surveyed_languages_realize_some_analysis :
    ∀ p ∈ surveyedLanguages, p.2.reductionRealized = true ∨ p.2.directRealized = true := by
  decide

/-- B&T's central typological observation: the surveyed languages
    populate three of the four cells of the 2×2 RA-by-DA grid; no two
    are identical. The unattested cell is ⟨false, false⟩ — no
    language is reported to lack both analyses. -/
theorem surveyed_languages_pairwise_distinct :
    surveyedLanguages.Pairwise (fun a b => a.2 ≠ b.2) := by
  decide

end BhattTakahashi2011
