import Linglib.Phenomena.Comparison.Studies.BhattPancheva2004
import Linglib.Phenomena.Comparison.Studies.Lechner2004
import Linglib.Theories.Interfaces.SyntaxSemantics.Minimalism.DegreeMovement

/-!
# Bhatt & Takahashi 2011: Reduced and Unreduced Phrasal Comparatives
@cite{bhatt-takahashi-2011} @cite{bhatt-pancheva-2004} @cite{bresnan-1973}
@cite{lechner-2001} @cite{lechner-2004} @cite{merchant-2009}
@cite{takahashi-hulsey-2009} @cite{heim-2006}

Rajesh Bhatt and Shoichi Takahashi. Reduced and Unreduced Phrasal
Comparatives. *Natural Language & Linguistic Theory* 29(3): 581–620.

## What this file is

A paper-faithful study of B&T 2011, the successor paper to
@cite{bhatt-pancheva-2004} that reverses B&P's central typological
claim about English phrasal comparatives. It also delivers the
diagnostic battery that the B&P 2004 file's closing prose flagged as
needed for a syntactic-structure verdict.

The diagnostic schema (`BindingDatum`, `RAPredictsCoref`,
`DAPredictsCoref`, `realizesReduction`, `realizesDirect`,
`HeadAvailability`, `headAvailabilityFromBinding`) lives in
`Lechner2004.lean` — B&T fn. 4 explicitly attributes (11)–(13) to
@cite{lechner-2004}'s disjoint-reference battery. This file imports
that schema and instantiates it on B&T's English and Hindi-Urdu data.

## B&T's two-analyses framework (§1)

Phrasal "John is taller than Bill" admits two competing analyses:

- **Reduction Analysis (RA)** — phrasal `than NP` derives from clausal
  `than [NP is Adj]` via reduction (gapping, conjunction reduction,
  TP-ellipsis, stripping). Uses the 2-place degree head, which combines
  with degree predicates.
- **Direct Analysis (DA)** — phrasal `than NP` is genuinely phrasal;
  the 'than'-phrase combines with an individual. Uses the 3-place
  degree head, which combines with two individuals plus a predicate of
  individuals and degrees.

## The walked-back B&P 2004 claim

@cite{bhatt-pancheva-2004} §1.1.1 fn. 4 rejected @cite{bresnan-1973}'s
reduction analysis of English phrasal comparatives. B&T 2011 §2's
binding diagnostic establishes the opposite for English: the standard
is c-commanded by everything that c-commands the associate, which is
the structural signature of RA, not DA. The 3-place '-er' is needed
for *Hindi-Urdu* §3, not English.

The cross-tradition bridge `bt2011_agrees_with_bresnan_against_bp2004`
witnesses that B&T's "reduction" and Bresnan's "maximal deletion" are
the same kind of analysis — both derive surface phrasal forms from
underlying clausal sources via deletion.

## The diagnostic battery (§2, §3.4)

The B&P 2004 file's closing note says formalizing the Bresnan
disagreement "would need either Bhatt & Takahashi 2011's diagnostic
battery or a richer syntactic interface." This file supplies the
former for the binding component:

- **§2** English binding generalization (B&T (10)) — six minimal-pair
  entries from B&T (11)–(13), checked against
  `realizesReduction` / `realizesDirect`.
- **§3.4** Hindi-Urdu binding contrast — captured by
  `hindiUrduBindingPairs` and the corresponding realization theorems.

Scope (§4), the Single Standard Restriction (§3.2), and the Precedence
Constraint (§3.3) are noted in prose; their formalization would
require richer syntactic infrastructure than the Lechner-style
binding minimal pairs.

## The typology proposal (B&T (63))

B&T's central crosslinguistic claim: both 2-place and 3-place degree
heads are universally available in principle. Crosslinguistic variation
in which is *realized* is determined by:

1. The **subcategorization** of the comparative marker (than / yori / -se):
   does it accept DPs, CPs, or both?
2. A **preference for minimal structure**: when a DP is locally
   available, the language prefers the smaller analysis.

For English and Hindi-Urdu the per-language `HeadAvailability` is
*derived* from the binding data via `headAvailabilityFromBinding`
(anti-stipulation). Japanese, where both analyses are realized, is
stipulated with an explicit comment: B&T's §5 multiple-standard
diagnostics (which would witness RA-realization for Japanese) require
infrastructure not present here.
-/

namespace BhattTakahashi2011

open Lechner2004 (BindingDatum RAPredictsCoref DAPredictsCoref
  realizesReduction realizesDirect HeadAvailability headAvailabilityFromBinding
  PhrasalAnalysis)
open Bresnan1973 (BresnanThanClauseAnalysis bresnanAnalysisOf)
open Features (Acceptability)
open Minimalism.Semantics.DegreeMovement
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

/-- B&T §2 English minimal pairs (11)–(13). Each pair contrasts a
    pronominal that c-commands the associate (blocking coref into the
    standard) with a no-c-command baseline (allowing coref).

    UNVERIFIED: judgments paraphrased; the binary pattern matches
    B&T's reported data. (13b) is recorded with `.marginal`
    acceptability per B&T fn. 5 (which describes some speakers as
    finding it "(?)mildly deviant" — `corefAttested := true` because
    the binding relation is licensed for the prediction direction). -/
def englishBindingPairs : List BindingDatum :=
  [-- B&T (11a): "*she_i introduced him to Mary's_i mother"
   { citationId := "11a", acceptability := .unacceptable
     pronCCommandsAssociate := true,  corefAttested := false },
   -- B&T (11b): "she_i is taller than Mary's_i mother (is)"
   { citationId := "11b", acceptability := .ok
     pronCCommandsAssociate := false, corefAttested := true },
   -- B&T (12a): "*he_i talked to her about Sally's_i sister"
   { citationId := "12a", acceptability := .unacceptable
     pronCCommandsAssociate := true,  corefAttested := false },
   -- B&T (12b): "he_i is smarter than Sally's_i sister (is)"
   { citationId := "12b", acceptability := .ok
     pronCCommandsAssociate := false, corefAttested := true },
   -- B&T (13a): the c-command-blocks-coref baseline
   { citationId := "13a", acceptability := .unacceptable
     pronCCommandsAssociate := true,  corefAttested := false },
   -- B&T (13b) per fn. 5: marginal but in the "coref licit" direction
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

    UNVERIFIED: B&T (35) supplies the key positive-coref-with-c-command
    example; the second entry is the no-c-command baseline. -/
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

/-- @cite{bhatt-pancheva-2004} §1.1.1 fn. 4's verdict for English,
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

/-- B&T §4 (43) English scope data. The structural prediction is RA's:
    than-internal scope is attested iff the QP's base position is at
    or below the DegP (B&T's "doesn't c-command the degree trace from
    the base").

    UNVERIFIED: examples paraphrased; the binary pattern matches
    B&T's reported English data. (44a) is the in-situ existential
    case (base = degH); (44b) is the raised universal blocking
    than-internal scope. -/
def englishScopeData : List ScopeDatum :=
  [-- B&T (44a): existential in situ inside than-XP, base = DegP height
   { citationId := "44a"
     binding := ⟨1, 1, 1, false⟩
     thanInternalScopeAttested := true },
   -- B&T (44b): raised universal, base position above DegP
   { citationId := "44b"
     binding := ⟨1, 2, 2, true⟩
     thanInternalScopeAttested := false }]

/-- B&T §4 (43) Hindi-Urdu scope data. RA predicts than-internal
    scope should be available for low-base QPs, but Hindi-Urdu
    *forces* scope-out: than-internal scope is unattested even when
    the base position is at or below the DegP.

    UNVERIFIED: data point reflects B&T §4.2's verdict that
    Hindi-Urdu obligatorily scopes out, not RA-internal scope. -/
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
    re-vindicates @cite{bresnan-1973}'s analysis of English phrasal
    comparatives (`maximalDeletion`) against
    @cite{bhatt-pancheva-2004}'s direct analysis. The agreement is at
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

/-- Japanese (B&T §5): both analyses realized. UNVERIFIED-AS-DERIVED:
    B&T's §5 argument that Japanese realizes RA rests on
    multiple-standard data and *yori*'s subcategorization for CPs;
    those diagnostics require infrastructure not present in this
    file. The DA-realization side could in principle be derived from
    Japanese binding data parallel to Hindi-Urdu's, but B&T do not
    give the relevant minimal pairs in the cited form. So Japanese is
    stipulated, with an explicit note that the derivation is owed. -/
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

/- ## What this file does not formalize

- **§3.2 Single Standard Restriction** (Hindi-Urdu allows exactly one
  standard per phrasal comparative). Statable as a `List Standard`
  with cardinality constraint, but the constraint is on Hindi-Urdu
  syntactic structure rather than on the diagnostic data points
  formalized above.
- **§3.3 Precedence Constraint** (Hindi-Urdu requires the associate
  to overtly precede '-er'). Requires an overt-linear-order interface
  not currently in scope.
- **§5 Japanese RA-realization derivation**. Multiple-standard data
  + *yori*'s CP subcategorization would witness RA-realization for
  Japanese; here we stipulate `japaneseHeadAvailability := ⟨true, true⟩`
  with an explicit comment.
- **§6 Subcategorization-and-minimal-structure derivation** of the
  typology. B&T derive the per-language realized availabilities from
  morphosyntactic properties of than / yori / -se plus a parsing economy
  constraint; we record the *outcomes* in `HeadAvailability` but do
  not derive them from a formalization of the subcategorization
  lexicon. -/

end BhattTakahashi2011
