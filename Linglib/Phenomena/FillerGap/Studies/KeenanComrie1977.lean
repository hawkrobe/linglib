import Linglib.Phenomena.FillerGap.Typology

/-!
# Keenan & Comrie (1977) @cite{keenan-comrie-1977}

Noun Phrase Accessibility and Universal Grammar. Linguistic Inquiry 8(1): 63–99.

Formalizes the three **Hierarchy Constraints** (HCs) and the derived
**Primary Relativization Constraint** (PRC) from @cite{keenan-comrie-1977},
verified against a subset of the paper's Table 1 data.

## Hierarchy Constraints

The paper proposes three constraints on how languages form relative clauses,
building on the Accessibility Hierarchy (AH):

    SU > DO > IO > OBL > GEN > OCOMP

- **HC₁**: A language must be able to relativize subjects.
- **HC₂ (Continuity)**: Any RC-forming strategy must apply to a continuous
  segment of the AH.
- **HC₃ (Cut-off)**: Strategies that apply at one point may cease at any
  lower point.

From HC₁ + HC₂, the **Primary Relativization Constraint** follows: if a
language's primary strategy (one that covers subjects) can apply to a low
position N, it can apply to all positions above N. Non-primary strategies
need not satisfy this — they may cover a continuous segment that excludes
subjects (e.g., the +case strategy covering IO–OCOMP but not SU–DO in
Welsh and Arabic).

## Multi-Strategy Profiles

The paper's key empirical contribution is showing that languages typically
have multiple relativization strategies, each covering a different contiguous
segment of the AH. The ±case distinction (whether the relative element bears
case marking) is the primary parameter distinguishing strategies.

## Data

Table 1 profiles are encoded with per-strategy, per-position accessibility
data. We include a representative subset covering the key patterns:
single-strategy (English, Malagasy), gap-to-resumptive split (Welsh, Hebrew,
Arabic, Toba Batak), and multi-strategy with prenominal RCs (Korean, Finnish).
-/

namespace Phenomena.FillerGap.Studies.KeenanComrie1977

open Phenomena.FillerGap.Typology

-- ============================================================================
-- § 1: Strategy Entry (Table 1 data format)
-- ============================================================================

/-- A single relativization strategy from @cite{keenan-comrie-1977} Table 1.

    Each language has one or more strategies. A strategy is characterized by
    the position of the RC (pre/post-nominal), whether the relative element
    bears case marking (±case), and which AH positions it covers. -/
structure StrategyEntry where
  /-- Position of relative clause with respect to head noun -/
  rcPosition : RelClausePosition
  /-- +case: the relative element (pronoun, relative pronoun) bears case
      marking for its role inside the RC. -case: no case-marked element
      in NP_rel (gap/deletion). -/
  plusCase : Bool
  su : Bool
  do_ : Bool
  io : Bool
  obl : Bool
  gen : Bool
  ocomp : Bool
  deriving DecidableEq, BEq, Repr

/-- Which AH position does this strategy cover? -/
def StrategyEntry.covers (s : StrategyEntry) : AHPosition → Bool
  | .subject        => s.su
  | .directObject   => s.do_
  | .indirectObject => s.io
  | .oblique        => s.obl
  | .genitive       => s.gen
  | .objComparison  => s.ocomp

/-- List of AH positions covered by this strategy. -/
def StrategyEntry.coveredPositions (s : StrategyEntry) : List AHPosition :=
  AHPosition.all.filter s.covers

/-- Is this a primary strategy? Primary strategies cover subjects.
    HC₁ requires at least one primary strategy per language. -/
def StrategyEntry.isPrimary (s : StrategyEntry) : Bool := s.su

/-- HC₂: Does this strategy cover a contiguous segment of the AH?
    Uses `contiguousOnAH` from `Typology.lean`, which mirrors the
    contiguity check in `Core.Case.Hierarchy.validInventory`. -/
def StrategyEntry.isContinuous (s : StrategyEntry) : Bool :=
  contiguousOnAH s.coveredPositions

-- ============================================================================
-- § 2: Language Profile
-- ============================================================================

/-- A language's full relativization profile from Table 1.
    Each language has one or more strategies covering (potentially
    overlapping) segments of the AH. -/
structure KCProfile where
  language : String
  strategies : List StrategyEntry
  notes : String := ""
  deriving Repr

/-- HC₁: The language can relativize subjects
    (at least one strategy covers SU). -/
def KCProfile.satisfiesHC1 (p : KCProfile) : Bool :=
  p.strategies.any (·.su)

/-- HC₂: Every strategy covers a contiguous segment of the AH. -/
def KCProfile.satisfiesHC2 (p : KCProfile) : Bool :=
  p.strategies.all (·.isContinuous)

/-- PRC: Every primary strategy satisfies upward closure — if it covers
    position N, it covers all positions above N. This follows from
    HC₂ (contiguity) + isPrimary (covers SU at rank 6): a contiguous
    segment containing rank 6 and rank N must contain all intermediate
    ranks. -/
def KCProfile.satisfiesPRC (p : KCProfile) : Bool :=
  p.strategies.all fun s =>
    if s.isPrimary then
      AHPosition.all.all fun pos =>
        if s.covers pos then
          AHPosition.all.all fun above =>
            if above.rank > pos.rank then s.covers above
            else true
        else true
    else true

-- ============================================================================
-- § 3: Table 1 Data (Representative Subset)
-- ============================================================================

-- The following data is from @cite{keenan-comrie-1977} Table 1 (pp. 76–79).
-- Languages explicitly discussed in the paper's text (§1.3) are marked;
-- others are read from the table. We include only positions clearly marked
-- + or - in the table; marginal cases (+/-, ?) are noted in comments.

/-- English: one -case strategy covering all AH positions.
    Postnominal RC with gap in NP_rel. -/
def english : KCProfile :=
  { language := "English"
  , strategies :=
      [ { rcPosition := .postNominal, plusCase := false
        , su := true, do_ := true, io := true
        , obl := true, gen := true, ocomp := true } ]
  , notes := "Single gap strategy covers all positions" }

/-- Welsh: two strategies (discussed §1.3.2).
    Primary (-case): gap with particle *a*, covers SU and DO.
    Secondary (+case): pronoun retention with particle *y*, covers IO–OCOMP. -/
def welsh : KCProfile :=
  { language := "Welsh"
  , strategies :=
      [ { rcPosition := .postNominal, plusCase := false
        , su := true, do_ := true, io := false
        , obl := false, gen := false, ocomp := false }
      , { rcPosition := .postNominal, plusCase := true
        , su := false, do_ := false, io := true
        , obl := true, gen := true, ocomp := true } ]
  , notes := "Gap+a for SU/DO; pronoun retention+y for IO–OCOMP (§1.3.2)" }

/-- Arabic (Classical): two strategies (discussed §1.3.2).
    Primary (-case): gap, covers SU only.
    Secondary (+case): pronoun retention, covers DO–OCOMP. -/
def arabic : KCProfile :=
  { language := "Arabic (Classical)"
  , strategies :=
      [ { rcPosition := .postNominal, plusCase := false
        , su := true, do_ := false, io := false
        , obl := false, gen := false, ocomp := false }
      , { rcPosition := .postNominal, plusCase := true
        , su := false, do_ := true, io := true
        , obl := true, gen := true, ocomp := true } ]
  , notes := "Gap for SU only; resumptive pronoun for DO–OCOMP (§1.3.2)" }

/-- Hebrew: two strategies (discussed §1.3.2).
    Primary (-case): gap, covers SU and DO.
    Secondary (+case): pronoun retention, covers DO–OCOMP.
    DO is shared between both strategies. -/
def hebrew : KCProfile :=
  { language := "Hebrew"
  , strategies :=
      [ { rcPosition := .postNominal, plusCase := false
        , su := true, do_ := true, io := false
        , obl := false, gen := false, ocomp := false }
      , { rcPosition := .postNominal, plusCase := true
        , su := false, do_ := true, io := true
        , obl := true, gen := true, ocomp := true } ]
  , notes := "Gap for SU/DO; resumptive for DO–OCOMP; DO covered by both" }

/-- Toba Batak: two strategies (discussed §1.3.2).
    Primary (-case): gap, covers SU only.
    Secondary (+case): pronoun retention, covers IO–GEN.
    DO cannot be relativized by either strategy — a genuine gap in AH
    coverage, noted explicitly in the paper. -/
def tobaBatak : KCProfile :=
  { language := "Toba Batak"
  , strategies :=
      [ { rcPosition := .postNominal, plusCase := false
        , su := true, do_ := false, io := false
        , obl := false, gen := false, ocomp := false }
      , { rcPosition := .postNominal, plusCase := true
        , su := false, do_ := false, io := true
        , obl := true, gen := true, ocomp := false } ]
  , notes := "Gap for SU; resumptive for IO–GEN; DO unreachable by either " ++
             "strategy (genuine gap, discussed §1.3.2)" }

/-- Korean: two strategies.
    Primary (-case): prenominal gap, covers SU–OBL.
    Secondary (+case): prenominal, covers GEN only. -/
def korean : KCProfile :=
  { language := "Korean"
  , strategies :=
      [ { rcPosition := .preNominal, plusCase := false
        , su := true, do_ := true, io := true
        , obl := true, gen := false, ocomp := false }
      , { rcPosition := .preNominal, plusCase := true
        , su := false, do_ := false, io := false
        , obl := false, gen := true, ocomp := false } ]
  , notes := "-case gap covers SU–OBL; +case covers GEN only" }

/-- Finnish: two strategies.
    Primary (+case): postnominal relative pronoun *joka* (declines for
    case), covers SU–GEN. OCOMP does not exist as a distinct category.
    Secondary (-case): prenominal participial, covers SU–DO. -/
def finnish : KCProfile :=
  { language := "Finnish"
  , strategies :=
      [ { rcPosition := .postNominal, plusCase := true
        , su := true, do_ := true, io := true
        , obl := true, gen := true, ocomp := false }
      , { rcPosition := .preNominal, plusCase := false
        , su := true, do_ := true, io := false
        , obl := false, gen := false, ocomp := false } ]
  , notes := "+case joka covers SU–GEN; -case participial covers SU–DO; " ++
             "OCOMP does not exist as distinct category" }

/-- Malagasy: one -case strategy covering SU only.
    Predicate-initial Austronesian language; only the pivot (subject)
    can be relativized; voice alternation required to relativize
    underlying non-subjects. -/
def malagasy : KCProfile :=
  { language := "Malagasy"
  , strategies :=
      [ { rcPosition := .postNominal, plusCase := false
        , su := true, do_ := false, io := false
        , obl := false, gen := false, ocomp := false } ]
  , notes := "Only pivot (subject) relativizable; voice alternation " ++
             "for non-SU; Austronesian extraction restriction" }

/-- All Table 1 profiles in our sample. -/
def allProfiles : List KCProfile :=
  [english, welsh, arabic, hebrew, tobaBatak, korean, finnish, malagasy]

-- ============================================================================
-- § 4: Hierarchy Constraint Verification
-- ============================================================================

/-- HC₁ holds: every language in our sample can relativize subjects. -/
theorem hc1_verified :
    allProfiles.all (·.satisfiesHC1) = true := by native_decide

/-- HC₂ holds: every strategy covers a contiguous segment of the AH. -/
theorem hc2_verified :
    allProfiles.all (·.satisfiesHC2) = true := by native_decide

/-- PRC holds: every primary strategy satisfies upward closure. -/
theorem prc_verified :
    allProfiles.all (·.satisfiesPRC) = true := by native_decide

-- ============================================================================
-- § 5: PRC as Consequence of HC₂ + Primary
-- ============================================================================

/-- The PRC follows from HC₂ for primary strategies: if a strategy is
    continuous and covers subjects (rank 6), then for any covered position
    at rank N, all positions with rank > N are also covered.

    We verify this structural implication on all strategies in our sample:
    isPrimary ∧ isContinuous → upward-closed. -/
theorem prc_follows_from_hc2_and_primary :
    allProfiles.all (λ p =>
      p.strategies.all (λ s =>
        if s.isPrimary && s.isContinuous then
          AHPosition.all.all (λ pos =>
            if s.covers pos then
              AHPosition.all.all (λ above =>
                if above.rank > pos.rank then s.covers above
                else true)
            else true)
        else true)) = true := by
  native_decide

/-- Every language has at least one primary strategy (restates HC₁
    in terms of the StrategyEntry.isPrimary predicate). -/
theorem every_language_has_primary :
    allProfiles.all (λ p =>
      p.strategies.any (·.isPrimary)) = true := by
  native_decide

-- ============================================================================
-- § 6: Cross-Linguistic Patterns
-- ============================================================================

/-- In our sample, every -case strategy covers subjects. The -case
    (gap/deletion) strategy is always primary when present. -/
theorem minus_case_covers_subjects :
    allProfiles.all (λ p =>
      p.strategies.all (λ s =>
        if !s.plusCase then s.su else true)) = true := by
  native_decide

/-- Multi-strategy languages: most languages in our sample use more
    than one strategy, with strategies covering different segments. -/
theorem most_have_multiple_strategies :
    (allProfiles.filter (λ p => p.strategies.length > 1)).length ≥ 5 := by
  native_decide

/-- +case strategies that are non-primary (don't cover SU) never cover
    SU in our sample. This reflects the typological generalization that
    pronoun retention is used for lower, not higher, AH positions. -/
theorem plus_case_secondary_excludes_su :
    allProfiles.all (λ p =>
      p.strategies.all (λ s =>
        if s.plusCase && !s.isPrimary then !s.su else true)) = true := by
  native_decide

/-- The gap-to-resumptive split: -case strategies always cover subjects,
    while +case secondary strategies never do. This means -case always
    occupies a strictly higher segment of the AH than non-primary +case. -/
theorem gap_covers_higher_than_resumptive :
    allProfiles.all (λ p =>
      p.strategies.all (λ s =>
        -- Every -case strategy covers SU
        (if !s.plusCase then s.su else true) &&
        -- Every non-primary +case strategy excludes SU
        (if s.plusCase && !s.isPrimary then !s.su else true))) = true := by
  native_decide

-- ============================================================================
-- § 7: Toba Batak DO Gap
-- ============================================================================

/-- Toba Batak has a genuine gap at DO: neither strategy can relativize
    direct objects. This is consistent with the HCs because each individual
    strategy is contiguous — the gap exists between strategies, not within
    one. The paper notes this explicitly. -/
theorem toba_batak_do_gap :
    tobaBatak.strategies.all (λ s => !s.do_) = true := by native_decide

/-- Despite the DO gap, both of Toba Batak's individual strategies are
    contiguous (SU alone; IO–GEN alone). HC₂ is satisfied. -/
theorem toba_batak_hc2 :
    tobaBatak.satisfiesHC2 = true := by native_decide

-- ============================================================================
-- § 8: Per-Profile Verification
-- ============================================================================

/-- English covers all 6 AH positions with one strategy. -/
theorem english_full_coverage :
    (english.strategies.map (·.coveredPositions.length)) = [6] := by native_decide

/-- Welsh splits at the DO/IO boundary: -case covers SU–DO, +case covers
    IO–OCOMP. Verified by checking coverage of each strategy. -/
theorem welsh_strategy_split :
    let s := welsh.strategies
    s.length = 2 ∧
    (s.map (·.su))   = [true, false] ∧
    (s.map (·.do_))  = [true, false] ∧
    (s.map (·.io))   = [false, true] ∧
    (s.map (·.ocomp)) = [false, true] := by native_decide

/-- Arabic (Classical): -case covers SU only. -/
theorem arabic_primary_su_only :
    let s := arabic.strategies
    (s.map (·.su))  = [true, false] ∧
    (s.map (·.do_)) = [false, true] := by native_decide

/-- Malagasy: single strategy, subject only. -/
theorem malagasy_su_only :
    malagasy.strategies.length = 1 ∧
    (malagasy.strategies.map (·.su))  = [true] ∧
    (malagasy.strategies.map (·.do_)) = [false] := by native_decide

/-- Korean: -case strategy covers SU–OBL but not GEN. -/
theorem korean_primary_su_to_obl :
    let s := korean.strategies
    (s.map (·.su))  = [true, false] ∧
    (s.map (·.obl)) = [true, false] ∧
    (s.map (·.gen)) = [false, true] := by native_decide

/-- Finnish: +case strategy is primary (covers SU) despite being +case.
    Finnish is an example where the +case strategy is the broader one. -/
theorem finnish_plus_case_is_primary :
    let s := finnish.strategies
    (s.map (·.plusCase))  = [true, false] ∧
    (s.map (·.isPrimary)) = [true, true] := by native_decide

-- ============================================================================
-- § 9: Connection to WALS Profiles
-- ============================================================================

/-- Cross-reference: the Welsh WALS profile in `Typology.lean` records
    `lowestRelativizable := .oblique`, but Table 1 shows the +case strategy
    covers all the way to OCOMP. The discrepancy reflects that WALS
    and Table 1 use different data sources and granularity — WALS Ch 123
    only asks about obliques, not the full AH. -/
theorem welsh_covers_ocomp_via_plus_case :
    (welsh.strategies.filter (·.plusCase)).any (·.ocomp) = true := by
  native_decide

/-- Sample size: 8 languages from Table 1. -/
theorem sample_size : allProfiles.length = 8 := by native_decide

end Phenomena.FillerGap.Studies.KeenanComrie1977
