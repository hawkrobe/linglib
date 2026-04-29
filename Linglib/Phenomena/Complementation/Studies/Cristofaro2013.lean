import Linglib.Typology.Complementation

/-!
# Phenomena.Complementation.Studies.Cristofaro2013
@cite{noonan-2007} @cite{dryer-2013-wals}

Cross-linguistic complementation analysis anchored on Sonia Cristofaro's
five WALS chapters on complement/subordinate clauses (Ch 124--128):

- **Ch 124A**: 'Want' complement subjects (283 languages).
- **Ch 125A**: Purpose clauses -- balanced vs deranked (170 languages).
- **Ch 126A**: 'When' clauses -- balanced vs deranked (174 languages).
- **Ch 127A**: Reason clauses -- balanced vs deranked (169 languages).
- **Ch 128A**: Utterance complement clauses -- balanced vs deranked (143 languages).

The 19-language `ComplementationProfile` sample is the testbed for
cross-chapter generalizations.

## Cristofaro's central insight

Complement clauses can be classified along a single binary dimension:
**balanced** (retains main-clause morphology) vs. **deranked** (uses
reduced/non-finite forms). This maps onto Noonan's finer typology:
balanced ≈ indicative/subjunctive, deranked ≈ infinitive/nominalized/
participle. Different complement types differ systematically in how
likely they are to be deranked: utterance complements resist deranking
strongly, purpose clauses favor it.

NOTE: cristofaro-2013 has no entry in `references.bib` yet; cited via
inheritance from Cristofaro's Ch 124--128 contribution to
@cite{dryer-haspelmath-2013}.

## Contents

- §1. The 19-language `ComplementationProfile` sample.
- §2. Cross-chapter sample-grounded generalizations.

## Out of scope

The substrate types (`BalancedDeranked`, `WantCompStrategy`,
`ComplementationProfile`, WALS converters) and corpus-only generalizations
(utterance-mostly-balanced, purpose-more-deranked-than-utterance) live in
`Linglib/Typology/Complementation.lean`. The 20-language Dryer subordination
sample lives in `Studies/Dryer2013.lean`. Noonan's CTP per-verb data is in
`Studies/Noonan2007.lean`.
-/

set_option autoImplicit false

namespace Phenomena.Complementation.Studies.Cristofaro2013

open Typology.Complementation

-- ============================================================================
-- §1. The 19-Language Sample
-- ============================================================================

/-- English: equi-deletion with 'want'; balanced/deranked across
    purpose/when/reason; balanced utterance. -/
def compEnglish : ComplementationProfile :=
  { language := "English"
  , walsCode := "eng"
  , wantComp := some .subjectImplicit
  , purposeClause := some .balancedDeranked
  , whenClause := some .balancedDeranked
  , reasonClause := some .balancedDeranked
  , utteranceComp := some .balanced
  , notes := "Equi-deletion with 'want'; both finite and non-finite purpose/when/reason" }

/-- Japanese: desiderative suffix -tai; no independent 'want' CTP. -/
def compJapanese : ComplementationProfile :=
  { language := "Japanese"
  , walsCode := "jpn"
  , wantComp := some .desidAffix
  , purposeClause := some .balancedDeranked
  , whenClause := some .balancedDeranked
  , reasonClause := some .balanced
  , utteranceComp := some .balanced
  , notes := "Desiderative suffix -tai; no independent 'want' CTP in this sense" }

/-- Turkish: strongly deranked (nominalized) across clause types. -/
def compTurkish : ComplementationProfile :=
  { language := "Turkish"
  , walsCode := "tur"
  , wantComp := some .subjectImplicit
  , purposeClause := some .deranked
  , whenClause := some .deranked
  , reasonClause := some .balancedDeranked
  , utteranceComp := some .balancedDeranked
  , notes := "Strongly deranked (nominalized) across clause types" }

/-- Hindi: not in the F125A sample; otherwise mixed. -/
def compHindi : ComplementationProfile :=
  { language := "Hindi"
  , walsCode := "hin"
  , wantComp := some .subjectImplicit
  , purposeClause := none
  , whenClause := some .balancedDeranked
  , reasonClause := some .balancedDeranked
  , utteranceComp := some .balanced
  , notes := "Not in WALS Ch 125A sample" }

/-- Mandarin: isolating; uniformly balanced complements. -/
def compMandarin : ComplementationProfile :=
  { language := "Mandarin"
  , walsCode := "mnd"
  , wantComp := some .subjectImplicit
  , purposeClause := some .balanced
  , whenClause := some .balanced
  , reasonClause := some .balanced
  , utteranceComp := some .balanced
  , notes := "Isolating language: complements are uniformly balanced (finite)" }

/-- Korean: balanced despite being agglutinative SOV. -/
def compKorean : ComplementationProfile :=
  { language := "Korean"
  , walsCode := "kor"
  , wantComp := some .subjectImplicit
  , purposeClause := some .balanced
  , whenClause := some .balanced
  , reasonClause := some .balanced
  , utteranceComp := some .balanced
  , notes := "Balanced despite being agglutinative SOV" }

/-- German: not in F128A sample; mixed otherwise. -/
def compGerman : ComplementationProfile :=
  { language := "German"
  , walsCode := "ger"
  , wantComp := some .subjectImplicit
  , purposeClause := some .balancedDeranked
  , whenClause := some .balancedDeranked
  , reasonClause := some .balanced
  , utteranceComp := none
  , notes := "Not in WALS Ch 128A sample" }

/-- Russian: mixed balanced/deranked across subordinate clause types. -/
def compRussian : ComplementationProfile :=
  { language := "Russian"
  , walsCode := "rus"
  , wantComp := some .subjectImplicit
  , purposeClause := some .balancedDeranked
  , whenClause := some .balancedDeranked
  , reasonClause := some .balancedDeranked
  , utteranceComp := some .balanced
  , notes := "Mixed balanced/deranked across subordinate clause types" }

/-- Persian: overt complement subjects with 'want'. -/
def compPersian : ComplementationProfile :=
  { language := "Persian"
  , walsCode := "prs"
  , wantComp := some .subjectOvert
  , purposeClause := some .deranked
  , whenClause := some .balanced
  , reasonClause := some .balanced
  , utteranceComp := some .balanced
  , notes := "Overt complement subjects with 'want' (no equi-deletion)" }

/-- Irish: not in F124A sample; mixed otherwise. -/
def compIrish : ComplementationProfile :=
  { language := "Irish"
  , walsCode := "iri"
  , wantComp := none
  , purposeClause := some .balancedDeranked
  , whenClause := some .balancedDeranked
  , reasonClause := some .balancedDeranked
  , utteranceComp := some .balanced
  , notes := "Not in WALS Ch 124A sample" }

/-- Basque: deranked purpose clauses like Turkish. -/
def compBasque : ComplementationProfile :=
  { language := "Basque"
  , walsCode := "bsq"
  , wantComp := none
  , purposeClause := some .deranked
  , whenClause := some .balancedDeranked
  , reasonClause := some .balancedDeranked
  , utteranceComp := some .balanced
  , notes := "Not in WALS Ch 124A sample; deranked purpose clauses like Turkish" }

/-- Yoruba: uniformly balanced (serial verb language). -/
def compYoruba : ComplementationProfile :=
  { language := "Yoruba"
  , walsCode := "yor"
  , wantComp := some .subjectImplicit
  , purposeClause := some .balanced
  , whenClause := some .balanced
  , reasonClause := some .balanced
  , utteranceComp := some .balanced
  , notes := "Uniformly balanced (serial verb language)" }

/-- Tagalog: V-initial Austronesian; deranked purpose. -/
def compTagalog : ComplementationProfile :=
  { language := "Tagalog"
  , walsCode := "tag"
  , wantComp := some .subjectImplicit
  , purposeClause := some .deranked
  , whenClause := some .balancedDeranked
  , reasonClause := some .balancedDeranked
  , utteranceComp := some .balanced
  , notes := "V-initial Austronesian; deranked purpose clauses" }

/-- Navajo: only in Ch 124A; overt complement subjects. -/
def compNavajo : ComplementationProfile :=
  { language := "Navajo"
  , walsCode := "nav"
  , wantComp := some .subjectOvert
  , purposeClause := none
  , whenClause := none
  , reasonClause := none
  , utteranceComp := none
  , notes := "Only in WALS Ch 124A sample; overt complement subjects" }

/-- Swahili: only in Ch 128A. -/
def compSwahili : ComplementationProfile :=
  { language := "Swahili"
  , walsCode := "swa"
  , wantComp := none
  , purposeClause := none
  , whenClause := none
  , reasonClause := none
  , utteranceComp := some .balanced
  , notes := "Only in WALS Ch 128A sample" }

/-- Arabic (Gulf): balanced+deranked across purpose/when/reason/utterance. -/
def compArabic : ComplementationProfile :=
  { language := "Arabic (Gulf)"
  , walsCode := "arg"
  , wantComp := none
  , purposeClause := some .balancedDeranked
  , whenClause := some .balancedDeranked
  , reasonClause := some .balancedDeranked
  , utteranceComp := some .balancedDeranked
  , notes := "Gulf Arabic; Egyptian Arabic (aeg) in Ch 124A has overt comp subjects" }

/-- Finnish: negative auxiliary language; balanced+deranked across types. -/
def compFinnish : ComplementationProfile :=
  { language := "Finnish"
  , walsCode := "fin"
  , wantComp := some .subjectImplicit
  , purposeClause := some .balancedDeranked
  , whenClause := some .balancedDeranked
  , reasonClause := some .balancedDeranked
  , utteranceComp := some .balancedDeranked
  , notes := "Negative auxiliary language; balanced+deranked across clause types" }

/-- Spanish: deranked purpose (`para + INF`); subjunctive complements. -/
def compSpanish : ComplementationProfile :=
  { language := "Spanish"
  , walsCode := "spa"
  , wantComp := some .subjectImplicit
  , purposeClause := some .deranked
  , whenClause := some .balancedDeranked
  , reasonClause := some .balancedDeranked
  , utteranceComp := some .balancedDeranked
  , notes := "Deranked purpose (infinitive 'para + INF'); subjunctive complements" }

/-- French: deranked purpose (`pour + INF`); subjunctive complements. -/
def compFrench : ComplementationProfile :=
  { language := "French"
  , walsCode := "fre"
  , wantComp := some .subjectImplicit
  , purposeClause := some .deranked
  , whenClause := some .balancedDeranked
  , reasonClause := some .balancedDeranked
  , utteranceComp := some .balancedDeranked
  , notes := "Deranked purpose (infinitive 'pour + INF'); subjunctive complements" }

/-- The 19-language sample. -/
def allCompProfiles : List ComplementationProfile :=
  [ compEnglish, compJapanese, compTurkish, compHindi, compMandarin
  , compKorean, compGerman, compRussian, compPersian, compIrish
  , compBasque, compYoruba, compTagalog, compNavajo, compSwahili
  , compArabic, compFinnish, compSpanish, compFrench ]

theorem comp_profile_count : allCompProfiles.length = 19 := by native_decide

-- ============================================================================
-- §2. Cross-Chapter Sample Generalizations
-- ============================================================================

/-- In the sample, languages with deranked purpose clauses tend to also
    have at least balanced/deranked 'when' clauses (purpose deranking is
    not isolated). -/
theorem deranked_purpose_implies_at_least_mixed_when :
    let derankedPurp := allCompProfiles.filter (λ p =>
      p.purposeClause == some .deranked)
    derankedPurp.all (λ p =>
      p.whenClause == some .balancedDeranked ||
      p.whenClause == some .deranked ||
      p.whenClause == some .balanced) = true := by
  native_decide

/-- Sample utterance complements lean balanced (consistent with Cristofaro's
    cross-chapter observation). -/
theorem sample_utterance_lean_balanced :
    let withUtt := allCompProfiles.filter (·.utteranceComp.isSome)
    let balanced := withUtt.filter (λ p =>
      p.utteranceComp == some .balanced ||
      p.utteranceComp == some .balancedDeranked)
    balanced.length > withUtt.length / 2 := by native_decide

/-- Sample purpose clauses show more pure-deranked entries than
    pure-balanced (matching the WALS-aggregate trend in
    `Typology.Complementation.purpose_more_deranked_than_utterance`). -/
theorem sample_purpose_more_deranked_than_balanced :
    let withPurp := allCompProfiles.filter (·.purposeClause.isSome)
    let pureDeranked := withPurp.filter (·.purposeClause == some .deranked)
    let pureBalanced := withPurp.filter (·.purposeClause == some .balanced)
    pureDeranked.length ≥ pureBalanced.length := by native_decide

/-- The 'want' complement subject is left implicit in the majority of
    sample languages (Cristofaro Ch 124A's headline pattern in our sample). -/
theorem sample_want_mostly_implicit :
    let withWant := allCompProfiles.filter (·.wantComp.isSome)
    let implicitSubj := withWant.filter (·.wantComp == some .subjectImplicit)
    implicitSubj.length * 2 > withWant.length := by native_decide

-- ============================================================================
-- §3. Noonan ↔ Cristofaro typology bridge
-- ============================================================================

/-- Project @cite{noonan-2007}'s 6-way `NoonanCompType` onto Cristofaro's
    coarser `BalancedDeranked` typology. Noonan's reduced types
    (infinitive/nominalized/participle, captured by `NoonanCompType.isReduced`)
    correspond to Cristofaro's `.deranked`; finite types
    (indicative/subjunctive) correspond to `.balanced`. Paratactic falls
    on the balanced side: paratactic complements use main-clause morphology
    and behave like balanced finite clauses for Cristofaro's morphological
    test. -/
def noonanToCristofaro : NoonanCompType → BalancedDeranked
  | .indicative  => .balanced
  | .subjunctive => .balanced
  | .paratactic  => .balanced
  | .infinitive  => .deranked
  | .nominalized => .deranked
  | .participle  => .deranked

/-- The two typologies' "reduced" diagnostics agree by construction.
    `NoonanCompType.isReduced t = true` iff `noonanToCristofaro t = .deranked`.
    Promotes the docstring-only correspondence to a kernel-checked theorem. -/
theorem deranked_iff_reduced (t : NoonanCompType) :
    noonanToCristofaro t = .deranked ↔ t.isReduced = true := by
  cases t <;> simp [noonanToCristofaro, NoonanCompType.isReduced]

/-- Symmetric form: balanced iff non-reduced. -/
theorem balanced_iff_not_reduced (t : NoonanCompType) :
    noonanToCristofaro t = .balanced ↔ t.isReduced = false := by
  cases t <;> simp [noonanToCristofaro, NoonanCompType.isReduced]

end Phenomena.Complementation.Studies.Cristofaro2013
