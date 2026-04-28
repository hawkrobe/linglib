import Linglib.Fragments.English.Relativization
import Linglib.Fragments.Welsh.Relativization
import Linglib.Fragments.Arabic.Relativization
import Linglib.Fragments.Hebrew.Relativization
import Linglib.Fragments.TobaBatak.Relativization
import Linglib.Fragments.Korean.Relativization
import Linglib.Fragments.Finnish.Relativization
import Linglib.Fragments.Malagasy.Relativization
import Linglib.Fragments.Yoruba.Relativization

/-!
# Keenan & Comrie (1977) @cite{keenan-comrie-1977}

Noun Phrase Accessibility and Universal Grammar. Linguistic Inquiry 8(1): 63–99.

Formalizes the three **Hierarchy Constraints** (HCs) and the derived
**Primary Relativization Constraint** (PRC) from @cite{keenan-comrie-1977},
verified against a subset of the paper's Table 1 data.

The per-language `KCProfile` entries below derive their data from
`Fragments/{Lang}/Relativization.lean`, which encode the markers documented
in @cite{keenan-comrie-1979} (the per-language exemplification appendix
originally intended for publication with K&C 1977 — Language 55(2): 333–351).
K&C 1977 Table 1 (pp. 76–79) codes ~50 languages with ±case/RC-position
labels and per-AH-position ±coverage; K&C 1979 provides sentence-level
examples for each Table 1 row. Inline @cite{keenan-comrie-1979} citations
live in the Fragment files where the descriptive markers are encoded.

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

Table 1 profiles are **derived from fragment data** — each language's
`RelClauseMarker` list (encoding actual linguistic markers: particles,
pronouns, verbal suffixes) is converted to `StrategyEntry` records.
This ensures the study file stays consistent with the fragment layer
by construction. We cover the key patterns: gap-to-resumptive split
(Welsh, Hebrew, Arabic, Toba Batak), multi-strategy with prenominal
RCs (Korean, Finnish), single-strategy (Malagasy), and per-position
strategy split with serial-verb-mediated obliques (Yoruba).
-/

namespace Phenomena.Relativization.Studies.KeenanComrie1977

open Core

-- ============================================================================
-- § 1: Strategy Entry (Table 1 data format)
-- ============================================================================

/-- A single relativization strategy from @cite{keenan-comrie-1977} Table 1.

    Each language has one or more strategies. A strategy is characterized by
    the position of the RC (pre/post-nominal), whether the relative element
    bears case marking (±case), and which AH positions it covers. -/
structure StrategyEntry where
  /-- Position of relative clause with respect to head noun -/
  rcPosition : RCPosition
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
  deriving DecidableEq, Repr

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
    Uses `contiguousOnAH` from `Core.Relativization.Hierarchy`, which mirrors
    the contiguity check in `Core.Case.Hierarchy.validInventory`. -/
def StrategyEntry.isContinuous (s : StrategyEntry) : Bool :=
  contiguousOnAH s.coveredPositions

/-- Convert a fragment's `RelClauseMarker` to a Table 1 `StrategyEntry`.
    The marker's `bearsCaseMarking` maps to ±case, and its `positions`
    list determines per-position coverage. -/
def RelClauseMarker.toStrategyEntry (m : RelClauseMarker) : StrategyEntry :=
  { rcPosition := m.rcPosition
  , plusCase := m.bearsCaseMarking
  , su := m.covers .subject
  , do_ := m.covers .directObject
  , io := m.covers .indirectObject
  , obl := m.covers .oblique
  , gen := m.covers .genitive
  , ocomp := m.covers .objComparison }

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

/-- Build a `KCProfile` from a language name and its fragment marker list. -/
def mkProfile (name : String) (markers : List RelClauseMarker)
    (notes : String := "") : KCProfile :=
  { language := name
  , strategies := markers.map RelClauseMarker.toStrategyEntry
  , notes := notes }

-- ============================================================================
-- § 3: Table 1 Data (Derived from Fragments)
-- ============================================================================

-- The following data is derived from fragment Relativization.lean files,
-- which encode actual linguistic markers (particles, pronouns, suffixes).
-- The conversion `RelClauseMarker.toStrategyEntry` maps each marker to
-- its Table 1 representation. Languages discussed in §1.3 are noted.
-- The Fragment files cite @cite{keenan-comrie-1979} inline where its
-- exemplifications back the descriptive marker data.

/-- English: two strategies derived from `Fragments.English.relMarkers`.
    -case: complementizer *that*/∅, gap, covers SU/DO.
    +case: relative pronoun *who/whom/which/whose*, covers IO–OCOMP. -/
def english : KCProfile :=
  mkProfile "English" Fragments.English.relMarkers
    "-case that/∅ for SU/DO; +case who/whom for IO–OCOMP"

/-- Welsh: two strategies derived from `Fragments.Welsh.relMarkers` (§1.3.2).
    -case: particle *a*, gap, covers SU/DO.
    +case: particle *y*, resumptive pronoun, covers IO–OCOMP. -/
def welsh : KCProfile :=
  mkProfile "Welsh" Fragments.Welsh.relMarkers
    "Gap+a for SU/DO; pronoun retention+y for IO–OCOMP (§1.3.2)"

/-- Arabic: two strategies derived from `Fragments.Arabic.relMarkers` (§1.3.2).
    -case: *alladhi*, gap, covers SU only.
    +case: resumptive pronoun, covers DO–OCOMP. -/
def arabic : KCProfile :=
  mkProfile "Arabic (Classical)" Fragments.Arabic.relMarkers
    "Gap for SU only; resumptive pronoun for DO–OCOMP (§1.3.2)"

/-- Hebrew: two strategies derived from `Fragments.Hebrew.relMarkers` (§1.3.2).
    -case: complementizer *she-*, gap, covers SU/DO.
    +case: *she-* + resumptive pronoun, covers DO–OCOMP.
    DO is shared between both strategies. -/
def hebrew : KCProfile :=
  mkProfile "Hebrew" Fragments.Hebrew.relMarkers
    "Gap for SU/DO; resumptive for DO–OCOMP; DO covered by both"

/-- Toba Batak: two strategies derived from `Fragments.TobaBatak.relMarkers`
    (§1.3.2). -case: gap, covers SU only.
    +case: resumptive pronoun, covers IO/OBL/GEN.
    DO cannot be relativized by either strategy — a genuine gap. -/
def tobaBatak : KCProfile :=
  mkProfile "Toba Batak" Fragments.TobaBatak.relMarkers
    ("Gap for SU; resumptive for IO–GEN; DO unreachable by either " ++
     "strategy (genuine gap, discussed §1.3.2)")

/-- Korean: two strategies derived from `Fragments.Korean.relMarkers`.
    -case: adnominal suffix *-(n)ɨn, -n, -l*, gap, covers SU–OBL.
    +case: genitive marker *-uy*, covers GEN only. -/
def korean : KCProfile :=
  mkProfile "Korean" Fragments.Korean.relMarkers
    "-case gap covers SU–OBL; +case covers GEN only"

/-- Finnish: two strategies derived from `Fragments.Finnish.relMarkers`.
    +case: relative pronoun *joka* (declines for case), covers SU–GEN.
    -case: prenominal participial, covers SU/DO.
    OCOMP does not exist as a distinct category in Finnish. -/
def finnish : KCProfile :=
  mkProfile "Finnish" Fragments.Finnish.relMarkers
    ("+case joka covers SU–GEN; -case participial covers SU–DO; " ++
     "OCOMP does not exist as distinct category")

/-- Malagasy: one strategy derived from `Fragments.Malagasy.relMarkers`.
    -case: gap, covers SU only. Voice alternation required for
    non-subject relativization. -/
def malagasy : KCProfile :=
  mkProfile "Malagasy" Fragments.Malagasy.relMarkers
    ("Only pivot (subject) relativizable; voice alternation " ++
     "for non-SU; Austronesian extraction restriction")

/-- Yoruba (Kwa, Nigeria): four Fragment markers derived from
    `Fragments.Yoruba.relMarkers`. K&C 1977 Table 1 p. 79 codes Yoruba as
    two strategies (postnom -case for SU+DO; postnom +case for GEN);
    IO/OBL/OComp coded as `*` per K&C's serial-verb-recasting analysis.
    Our Fragment encodes per-position (4 markers), more granular than K&C's
    ±case-grouped Table 1; the underlying typological information is the same.
    SU is -case (consistent with K&C's verb-agreement analysis of `ó`). -/
def yoruba : KCProfile :=
  mkProfile "Yoruba" Fragments.Yoruba.relMarkers
    ("-case gap for DO (Awobuluyi §6.20) and IO/OBL (§6.21–22; K&C 1979 " ++
     "serial-verb recasting); -case resumptive for SU (ó, §6.19; K&C 1979 " ++
     "analyzes ó as agreement); +case resumptive for GEN (rẹ̀/wọn, §6.23). " ++
     "K&C 1977 Table 1 p. 79.")

/-- The original 8-language sub-sample, prior to Yoruba registration. Theorems
    referencing this list document empirical generalizations that held for
    the pre-Yoruba sample but may not generalize. Yoruba was added subsequently
    based on @cite{awobuluyi-1978} + @cite{keenan-comrie-1979}, and refutes
    two such generalizations (see `yoruba_refutes_*` theorems below). -/
def originalSample : List KCProfile :=
  [english, welsh, arabic, hebrew, tobaBatak, korean, finnish, malagasy]

/-- All Table 1 profiles in our sample (originalSample + Yoruba). -/
def allProfiles : List KCProfile :=
  originalSample ++ [yoruba]

-- ============================================================================
-- § 4: Hierarchy Constraint Verification
-- ============================================================================

/-- HC₁ holds: every language in our sample can relativize subjects. -/
theorem hc1_verified :
    allProfiles.all (·.satisfiesHC1) = true := by decide

/-- HC₂ holds: every strategy covers a contiguous segment of the AH. -/
theorem hc2_verified :
    allProfiles.all (·.satisfiesHC2) = true := by decide

/-- PRC holds: every primary strategy satisfies upward closure. -/
theorem prc_verified :
    allProfiles.all (·.satisfiesPRC) = true := by decide

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
  decide

/-- Every language has at least one primary strategy (restates HC₁
    in terms of the StrategyEntry.isPrimary predicate). -/
theorem every_language_has_primary :
    allProfiles.all (λ p =>
      p.strategies.any (·.isPrimary)) = true := by
  decide

-- ============================================================================
-- § 6: Cross-Linguistic Patterns
-- ============================================================================

/-- In the original 8-language sub-sample (pre-Yoruba), every -case strategy
    covers subjects. The -case (gap/deletion) strategy is always primary
    when present in those languages. **REFUTED by Yoruba** — see
    `yoruba_refutes_minus_case_covers_subjects` below: Yoruba has gap
    strategies for DO and OBL that do not cover SU, because subject
    relativization independently uses pronoun retention (`ó`). -/
theorem minus_case_covers_subjects_in_original_sample :
    originalSample.all (λ p =>
      p.strategies.all (λ s =>
        if !s.plusCase then s.su else true)) = true := by
  decide

/-- @cite{keenan-comrie-1979} effectively documents Yoruba as a refutation
    of the gap-implies-subject correlation. Yoruba's IO/OBL relativization
    is mediated by serial-verb DO recasting (K&C 1979 p. 349), producing
    -case strategies that do not cover SU. SU relativization independently
    uses pronoun retention (`ó`, K&C 1979 p. 350 analyzes as verb agreement;
    descriptive surface form per @cite{awobuluyi-1978} §6.19). -/
theorem yoruba_refutes_minus_case_covers_subjects :
    yoruba.strategies.any (λ s => !s.plusCase && !s.su) = true := by
  decide

/-- Multi-strategy languages: most languages in our sample use more
    than one strategy, with strategies covering different segments. -/
theorem most_have_multiple_strategies :
    (allProfiles.filter (λ p => p.strategies.length > 1)).length ≥ 5 := by
  decide

/-- +case strategies that are non-primary (don't cover SU) never cover
    SU in our sample. This reflects the typological generalization that
    pronoun retention is used for lower, not higher, AH positions.
    Holds across all 9 languages including Yoruba. -/
theorem plus_case_secondary_excludes_su :
    allProfiles.all (λ p =>
      p.strategies.all (λ s =>
        if s.plusCase && !s.isPrimary then !s.su else true)) = true := by
  decide

/-- The gap-to-resumptive split in the original 8-language sub-sample:
    -case strategies always cover subjects, while +case secondary strategies
    never do. **PARTIALLY REFUTED by Yoruba**: -case strategies do not always
    cover SU (Yoruba's DO/OBL gap strategies don't include SU). The
    +case-secondary-excludes-SU half of the conjunction still holds for
    Yoruba (see `plus_case_secondary_excludes_su` above). -/
theorem gap_covers_higher_than_resumptive_in_original_sample :
    originalSample.all (λ p =>
      p.strategies.all (λ s =>
        -- Every -case strategy covers SU
        (if !s.plusCase then s.su else true) &&
        -- Every non-primary +case strategy excludes SU
        (if s.plusCase && !s.isPrimary then !s.su else true))) = true := by
  decide

-- ============================================================================
-- § 7: Toba Batak DO Gap
-- ============================================================================

/-- Toba Batak has a genuine gap at DO: neither strategy can relativize
    direct objects. This is consistent with the HCs because each individual
    strategy is contiguous — the gap exists between strategies, not within
    one. The paper notes this explicitly. -/
theorem toba_batak_do_gap :
    tobaBatak.strategies.all (λ s => !s.do_) = true := by decide

/-- Despite the DO gap, both of Toba Batak's individual strategies are
    contiguous (SU alone; IO–GEN alone). HC₂ is satisfied. -/
theorem toba_batak_hc2 :
    tobaBatak.satisfiesHC2 = true := by decide

-- ============================================================================
-- § 8: Per-Profile Verification
-- ============================================================================

/-- English covers all 6 AH positions across two strategies:
    -case (that/∅) covers SU/DO (2), +case (who/whom) covers IO–OCOMP (4). -/
theorem english_full_coverage :
    (english.strategies.map (·.coveredPositions.length)) = [2, 4] := by decide

/-- Welsh splits at the DO/IO boundary: -case covers SU–DO, +case covers
    IO–OCOMP. Verified by checking coverage of each strategy. -/
theorem welsh_strategy_split :
    let s := welsh.strategies
    s.length = 2 ∧
    (s.map (·.su))   = [true, false] ∧
    (s.map (·.do_))  = [true, false] ∧
    (s.map (·.io))   = [false, true] ∧
    (s.map (·.ocomp)) = [false, true] := by decide

/-- Arabic (Classical): -case covers SU only. -/
theorem arabic_primary_su_only :
    let s := arabic.strategies
    (s.map (·.su))  = [true, false] ∧
    (s.map (·.do_)) = [false, true] := by decide

/-- Malagasy: single strategy, subject only. -/
theorem malagasy_su_only :
    malagasy.strategies.length = 1 ∧
    (malagasy.strategies.map (·.su))  = [true] ∧
    (malagasy.strategies.map (·.do_)) = [false] := by decide

/-- Korean: -case strategy covers SU–OBL but not GEN. -/
theorem korean_primary_su_to_obl :
    let s := korean.strategies
    (s.map (·.su))  = [true, false] ∧
    (s.map (·.obl)) = [true, false] ∧
    (s.map (·.gen)) = [false, true] := by decide

/-- Finnish: +case strategy is primary (covers SU) despite being +case.
    Finnish is an example where the +case strategy is the broader one. -/
theorem finnish_plus_case_is_primary :
    let s := finnish.strategies
    (s.map (·.plusCase))  = [true, false] ∧
    (s.map (·.isPrimary)) = [true, true] := by decide

/-- Yoruba: four per-position markers; SU and GEN use resumption (relTiSubject
    is -case per K&C's verb-agreement analysis; relTiGenitive is +case);
    DO and OBL use gap (-case). All four strategies are individually
    contiguous on the AH, so HC₂ is satisfied. -/
theorem yoruba_strategy_breakdown :
    let s := yoruba.strategies
    s.length = 4 ∧
    (s.map (·.plusCase))  = [false, false, false, true] ∧
    (s.map (·.isPrimary)) = [true, false, false, false] := by decide

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
  decide

/-- Sample size: 9 languages (8 originalSample + Yoruba). -/
theorem sample_size : allProfiles.length = 9 := by decide

-- ============================================================================
-- § 10: Cross-System Connection (KCProfile ↔ RelativizationProfile)
-- ============================================================================

-- The two representations encode complementary views of the same data:
-- KCProfile (Table 1): multi-strategy, per-position coverage
-- RelativizationProfile (WALS): single-row summary, lowestRelativizable
--
-- The following theorems verify agreement between the two systems
-- for languages that appear in both.

/-- Lowest AH position covered by any strategy in a KCProfile.
    Returns the position with the smallest rank that is covered by
    at least one strategy. Returns `.subject` if nothing else matches. -/
def KCProfile.lowestCovered (p : KCProfile) : AHPosition :=
  let covers (pos : AHPosition) := p.strategies.any (·.covers pos)
  if covers .objComparison then .objComparison
  else if covers .genitive then .genitive
  else if covers .oblique then .oblique
  else if covers .indirectObject then .indirectObject
  else if covers .directObject then .directObject
  else .subject

/-- English: KCProfile covers all 6 positions (lowestCovered = OCOMP),
    matching `Fragments.English.relativization.lowestRelativizable = .objComparison`. -/
theorem english_kc_matches_wals :
    english.lowestCovered = .objComparison ∧
    Fragments.English.relativization.lowestRelativizable = .objComparison := by decide

/-- Welsh: KCProfile covers down to OCOMP (via +case strategy),
    though WALS records `.oblique` (Ch 123 only asks about obliques). -/
theorem welsh_kc_covers_deeper_than_wals :
    welsh.lowestCovered = .objComparison ∧
    Fragments.Welsh.relativization.lowestRelativizable = .oblique ∧
    AHPosition.moreAccessible .oblique .objComparison := by decide

/-- Korean: KCProfile covers SU-OBL + GEN, lowest = GEN.
    WALS records `.oblique` (doesn't track GEN). -/
theorem korean_kc_covers_deeper_than_wals :
    korean.lowestCovered = .genitive ∧
    Fragments.Korean.relativization.lowestRelativizable = .oblique := by decide

/-- Malagasy: both systems agree — subjects only. -/
theorem malagasy_kc_matches_wals :
    malagasy.lowestCovered = .subject ∧
    Fragments.Malagasy.relativization.lowestRelativizable = .subject := by decide

/-- Finnish: KCProfile covers SU-GEN (via joka), WALS records `.oblique`.
    Both agree that Finnish covers at least obliques. -/
theorem finnish_kc_matches_wals :
    finnish.lowestCovered = .genitive ∧
    Fragments.Finnish.relativization.lowestRelativizable = .oblique := by decide

/-- Hebrew: KCProfile covers all positions via +case (DO-OCOMP).
    WALS records `.oblique`. -/
theorem hebrew_kc_covers_deeper_than_wals :
    hebrew.lowestCovered = .objComparison ∧
    Fragments.Hebrew.relativization.lowestRelativizable = .oblique := by decide

/-- Arabic: KCProfile covers all positions (SU via gap, DO-OCOMP via resumptive).
    WALS records `.oblique`. -/
theorem arabic_kc_covers_deeper_than_wals :
    arabic.lowestCovered = .objComparison ∧
    Fragments.Arabic.relativization.lowestRelativizable = .oblique := by decide

/-- Yoruba: both systems agree at GEN. K&C 1977 Table 1's `*` codes for
    IO/OBL/OComp reflect serial-verb-mediated recasting (an analytical move),
    not a directly-described data point — so the Fragment's
    `lowestRelativizable := .genitive` (per Awobuluyi §6.23) and
    KCProfile's `lowestCovered = .genitive` (per the directly-described
    relTiGenitive marker) coincide. -/
theorem yoruba_kc_matches_wals :
    yoruba.lowestCovered = .genitive ∧
    Fragments.Yoruba.relativization.lowestRelativizable = .genitive := by decide

/-- **Systematic coverage agreement**: for every language in our sample
    that also appears in the WALS typology, the KCProfile covers at
    least as much as the WALS profile indicates. The WALS profile never
    claims a language can relativize a position that Table 1 doesn't
    cover — Table 1 is strictly more detailed. -/
theorem kc_at_least_as_detailed_as_wals :
    -- English
    english.lowestCovered.rank ≤ Fragments.English.relativization.lowestRelativizable.rank ∧
    -- Welsh
    welsh.lowestCovered.rank ≤ Fragments.Welsh.relativization.lowestRelativizable.rank ∧
    -- Korean
    korean.lowestCovered.rank ≤ Fragments.Korean.relativization.lowestRelativizable.rank ∧
    -- Malagasy
    malagasy.lowestCovered.rank ≤ Fragments.Malagasy.relativization.lowestRelativizable.rank ∧
    -- Finnish
    finnish.lowestCovered.rank ≤ Fragments.Finnish.relativization.lowestRelativizable.rank ∧
    -- Hebrew
    hebrew.lowestCovered.rank ≤ Fragments.Hebrew.relativization.lowestRelativizable.rank ∧
    -- Arabic
    arabic.lowestCovered.rank ≤ Fragments.Arabic.relativization.lowestRelativizable.rank ∧
    -- Yoruba
    yoruba.lowestCovered.rank ≤ Fragments.Yoruba.relativization.lowestRelativizable.rank := by
  decide

end Phenomena.Relativization.Studies.KeenanComrie1977
