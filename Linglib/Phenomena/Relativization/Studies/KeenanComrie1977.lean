import Linglib.Core.Relativization.Hierarchy
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
verified against a subset of the paper's Table 1 data (pp. 76-79).

## Architecture

This file derives K&C's typological theorems **directly from**
`Fragments.{Lang}.relMarkers : List RelClauseMarker`, the per-language
data layer encoding actual linguistic markers (particles, pronouns,
verbal suffixes). No intermediate `KCProfile`/`StrategyEntry` schema —
predicates and aggregations are stated over `List RelClauseMarker`
directly, projecting through `RelClauseMarker.{positions,
bearsCaseMarking, rcPosition}` as needed.

The Fragment files cite @cite{keenan-comrie-1979} (the per-language
exemplification appendix originally intended for publication with K&C
1977 — Language 55(2): 333–351) inline where its sentence-level examples
back the descriptive marker data.

## Hierarchy Constraints

The paper proposes three constraints on how languages form relative clauses,
building on the Accessibility Hierarchy (AH):

    SU > DO > IO > OBL > GEN > OCOMP

- **HC₁** (p. 67): A language must be able to relativize subjects.
- **HC₂ (Continuity)** (p. 67): Any RC-forming strategy must apply to a
  continuous segment of the AH.
- **HC₃ (Cut-off)** (p. 67): Strategies that apply at one point may cease
  at any lower point.

From HC₁ + HC₂, the **Primary Relativization Constraint** (p. 68)
follows: if a language's primary strategy (one that covers subjects) can
apply to a low position N, it can apply to all positions above N.
Non-primary strategies need not satisfy this — they may cover a continuous
segment that excludes subjects (e.g., the +case strategy covering IO–OCOMP
but not SU–DO in Welsh and Arabic, p. 70 + Table 1 p. 76).

## Multi-Strategy Profiles

The paper's key empirical contribution is showing that languages typically
have multiple relativization strategies, each covering a different contiguous
segment of the AH. The ±case distinction (whether the relative element bears
case marking) is the primary parameter distinguishing strategies.

## Sample

Nine languages cover the key patterns: gap-to-resumptive split (Welsh,
Hebrew, Arabic, Toba Batak), multi-strategy with prenominal RCs (Korean,
Finnish), single-strategy (Malagasy), and per-position strategy split
with serial-verb-mediated obliques (Yoruba).
-/

namespace Phenomena.Relativization.Studies.KeenanComrie1977

open Core

-- ============================================================================
-- § 1: Predicates over List RelClauseMarker
-- ============================================================================

/-- HC₁: a language can relativize subjects iff some marker covers SU. -/
def SatisfiesHC1 (markers : List RelClauseMarker) : Prop :=
  ∃ m ∈ markers, m.Covers .subject

instance (markers : List RelClauseMarker) : Decidable (SatisfiesHC1 markers) := by
  unfold SatisfiesHC1; infer_instance

/-- HC₂: every marker covers a contiguous segment of the AH. -/
def SatisfiesHC2 (markers : List RelClauseMarker) : Prop :=
  ∀ m ∈ markers, m.IsContinuous

instance (markers : List RelClauseMarker) : Decidable (SatisfiesHC2 markers) := by
  unfold SatisfiesHC2; infer_instance

/-- PRC: every primary marker is upward-closed on the AH. If marker `m`
    is primary and covers position `pos`, then `m` covers every position
    above `pos`. This is the paper's Primary Relativization Constraint
    (p. 68), which follows from HC₂ for primary strategies (see
    `prc_from_hc2` below for the general derivation). -/
def SatisfiesPRC (markers : List RelClauseMarker) : Prop :=
  ∀ m ∈ markers, m.IsPrimary →
    ∀ pos ∈ AHPosition.all, m.Covers pos →
      ∀ above ∈ AHPosition.all, above.rank > pos.rank → m.Covers above

instance (markers : List RelClauseMarker) : Decidable (SatisfiesPRC markers) := by
  unfold SatisfiesPRC; infer_instance

/-- The lowest AH position covered by any marker in the list (i.e., the
    deepest the language can reach). Returns `.subject` if even SU is
    uncovered (vacuously, since HC₁ would be violated). -/
def lowestCovered (markers : List RelClauseMarker) : AHPosition :=
  let coversAny (pos : AHPosition) := markers.any (·.covers pos)
  if coversAny .objComparison then .objComparison
  else if coversAny .genitive then .genitive
  else if coversAny .oblique then .oblique
  else if coversAny .indirectObject then .indirectObject
  else if coversAny .directObject then .directObject
  else .subject

-- ============================================================================
-- § 2: Sample (per-language Fragment data)
-- ============================================================================

/-! Per-language abbrevs over Fragment marker lists. The original
8-language sample from the paper plus Yoruba (added later via
@cite{awobuluyi-1978} + @cite{keenan-comrie-1979}). -/

abbrev english   := Fragments.English.relMarkers
abbrev welsh     := Fragments.Welsh.relMarkers
abbrev arabic    := Fragments.Arabic.relMarkers
abbrev hebrew    := Fragments.Hebrew.relMarkers
abbrev tobaBatak := Fragments.TobaBatak.relMarkers
abbrev korean    := Fragments.Korean.relMarkers
abbrev finnish   := Fragments.Finnish.relMarkers
abbrev malagasy  := Fragments.Malagasy.relMarkers
abbrev yoruba    := Fragments.Yoruba.relMarkers

/-- The 8-language sub-sample from the original paper Table 1 (pp. 76-79). -/
def originalSample : List (List RelClauseMarker) :=
  [english, welsh, arabic, hebrew, tobaBatak, korean, finnish, malagasy]

/-- The original 8-language sample plus Yoruba (the only post-1977
    addition; refutes one of the paper's implicit ±case generalizations
    — see `yoruba_refutes_minus_case_covers_subjects` below). -/
def allSamples : List (List RelClauseMarker) :=
  originalSample ++ [yoruba]

theorem sample_size : allSamples.length = 9 := by decide

-- ============================================================================
-- § 3: Hierarchy Constraint Verification on Sample
-- ============================================================================

/-- **HC₁** holds: every language in the sample can relativize subjects. -/
theorem hc1_verified :
    ∀ markers ∈ allSamples, SatisfiesHC1 markers := by decide

/-- **HC₂** holds: every marker in every sampled language covers a
    contiguous AH segment. -/
theorem hc2_verified :
    ∀ markers ∈ allSamples, SatisfiesHC2 markers := by decide

/-- **PRC** holds: every primary marker satisfies upward closure on the AH. -/
theorem prc_verified :
    ∀ markers ∈ allSamples, SatisfiesPRC markers := by decide

/-- Restating HC₁ in terms of `RelClauseMarker.IsPrimary`: every language
    has at least one primary marker. -/
theorem every_language_has_primary :
    ∀ markers ∈ allSamples, ∃ m ∈ markers, m.IsPrimary := by decide

-- ============================================================================
-- § 4: Cross-Linguistic Patterns
-- ============================================================================

/-- In the original 8-language sub-sample, every -case marker covers
    subjects. The -case (gap/deletion) strategy is always primary when
    present in those languages.

    **REFUTED by Yoruba** — see `yoruba_refutes_minus_case_covers_subjects`
    below: Yoruba has gap markers for DO and OBL that do not cover SU
    because subject relativization independently uses pronoun retention
    (`ó`, per @cite{awobuluyi-1978} §6.19). -/
theorem minus_case_covers_subjects_in_original_sample :
    ∀ markers ∈ originalSample,
      ∀ m ∈ markers, m.bearsCaseMarking = false → m.Covers .subject := by
  decide

/-- @cite{keenan-comrie-1979} effectively documents Yoruba as a refutation
    of the gap-implies-subject correlation. Yoruba's IO/OBL relativization
    is mediated by serial-verb DO recasting (K&C 1979 p. 349), producing
    -case markers that do not cover SU. SU relativization independently
    uses pronoun retention (`ó`, K&C 1979 p. 350 analyzes as verb
    agreement; descriptive surface form per @cite{awobuluyi-1978} §6.19). -/
theorem yoruba_refutes_minus_case_covers_subjects :
    ∃ m ∈ yoruba, m.bearsCaseMarking = false ∧ ¬ m.Covers .subject := by
  decide

/-- Most languages in the sample use more than one marker, with markers
    covering different segments. -/
theorem most_have_multiple_strategies :
    (allSamples.filter (·.length > 1)).length ≥ 5 := by decide

/-- +case markers that are non-primary (don't cover SU) never cover SU
    in our sample. This reflects the typological generalization that
    pronoun retention is used for lower, not higher, AH positions.
    Holds across all 9 languages including Yoruba. -/
theorem plus_case_secondary_excludes_su :
    ∀ markers ∈ allSamples,
      ∀ m ∈ markers, m.bearsCaseMarking = true → ¬ m.IsPrimary →
        ¬ m.Covers .subject := by decide

-- ============================================================================
-- § 5: Toba Batak DO Gap (paper p. 68-69, canonical example)
-- ============================================================================

/-- Toba Batak has a genuine gap at DO: neither marker can relativize
    direct objects. This is consistent with the HCs because each
    individual marker is contiguous — the gap exists *between* markers,
    not within one. The paper notes this explicitly (p. 68-69: "direct
    objects cannot be relativized using this or any other strategy in
    Toba"). -/
theorem toba_batak_do_gap :
    ∀ m ∈ tobaBatak, ¬ m.Covers .directObject := by decide

/-- Despite the DO gap, Toba Batak satisfies HC₂: both individual markers
    are contiguous (SU alone; IO–GEN alone). -/
theorem toba_batak_hc2 : SatisfiesHC2 tobaBatak := by decide

-- ============================================================================
-- § 6: Per-Language Verification (Table 1 data, pp. 76-79)
-- ============================================================================

/-- English (Table 1 p. 76): -case `that/∅` covers SU/DO (2 positions);
    +case `who/whom` covers IO/OBL/GEN/OCOMP (4 positions). -/
theorem english_full_coverage :
    (english.map (·.positions.length)) = [2, 4] := by decide

/-- Welsh (Table 1 p. 76; paper §1.3.2 p. 70): markers split at DO/IO.
    -case (particle *a*) covers SU/DO; +case (particle *y* + resumptive)
    covers IO/OBL/GEN/OCOMP. -/
theorem welsh_strategy_split :
    welsh.length = 2 ∧
    (welsh.map (·.covers .subject))        = [true, false] ∧
    (welsh.map (·.covers .directObject))   = [true, false] ∧
    (welsh.map (·.covers .indirectObject)) = [false, true] ∧
    (welsh.map (·.covers .objComparison))  = [false, true] := by decide

/-- Arabic Classical (Table 1 p. 76): -case complementizer covers SU only;
    +case complementizer + resumptive covers DO–OCOMP. -/
theorem arabic_primary_su_only :
    (arabic.map (·.covers .subject))      = [true, false] ∧
    (arabic.map (·.covers .directObject)) = [false, true] := by decide

/-- Malagasy (Table 1 p. 78; paper §1.3.1 p. 69-70): single marker, SU only. -/
theorem malagasy_su_only :
    malagasy.length = 1 ∧
    (malagasy.map (·.covers .subject))      = [true] ∧
    (malagasy.map (·.covers .directObject)) = [false] := by decide

/-- Korean (Table 1 p. 78; paper §1.3.4 p. 74): -case adnominal verb
    suffix covers SU/DO/IO/OBL but not GEN; +case genitive marker covers
    GEN only. -/
theorem korean_primary_su_to_obl :
    (korean.map (·.covers .subject))  = [true, false] ∧
    (korean.map (·.covers .oblique))  = [true, false] ∧
    (korean.map (·.covers .genitive)) = [false, true] := by decide

/-- Finnish (Table 1 p. 76; paper §1.3.2 p. 70-71): the +case marker
    *joka* is the broader/primary one (covers SU–GEN); the -case
    participial marker also covers SU but is narrower (SU/DO only). -/
theorem finnish_plus_case_is_primary :
    (finnish.map (·.bearsCaseMarking)) = [true, false] ∧
    (finnish.map (·.isPrimary))        = [true, true] := by decide

/-- Yoruba: 4 per-position markers. relTiSubject (-case, primary, only
    SU); relTiObject (-case, NOT primary, only DO); relTiOblique (-case,
    NOT primary, IO/OBL); relTiGenitive (+case, NOT primary, GEN only).
    All 4 individually contiguous on the AH, so HC₂ holds. -/
theorem yoruba_strategy_breakdown :
    yoruba.length = 4 ∧
    (yoruba.map (·.bearsCaseMarking)) = [false, false, false, true] ∧
    (yoruba.map (·.isPrimary))        = [true, false, false, false] := by decide

-- ============================================================================
-- § 7: Bridge to RelativizationProfile (Typology layer)
-- ============================================================================

/-! K&C 1977 Table 1's per-position coverage and `RelativizationProfile`'s
WALS-derived `lowestRelativizable` encode complementary views of the same
data. Bridge theorems below verify agreement on the lowest position
covered, language by language. K&C's Table 1 is strictly more detailed
than WALS Ch 122/123 (which only ask about subjects and obliques), so
the K&C `lowestCovered` is at least as deep as the WALS
`lowestRelativizable`. -/

theorem english_kc_matches_wals :
    lowestCovered english = .objComparison ∧
    Fragments.English.relativization.lowestRelativizable = .objComparison := by decide

theorem welsh_kc_covers_deeper_than_wals :
    lowestCovered welsh = .objComparison ∧
    Fragments.Welsh.relativization.lowestRelativizable = .oblique ∧
    AHPosition.moreAccessible .oblique .objComparison := by decide

theorem korean_kc_covers_deeper_than_wals :
    lowestCovered korean = .genitive ∧
    Fragments.Korean.relativization.lowestRelativizable = .oblique := by decide

theorem malagasy_kc_matches_wals :
    lowestCovered malagasy = .subject ∧
    Fragments.Malagasy.relativization.lowestRelativizable = .subject := by decide

theorem finnish_kc_matches_wals :
    lowestCovered finnish = .genitive ∧
    Fragments.Finnish.relativization.lowestRelativizable = .oblique := by decide

theorem hebrew_kc_covers_deeper_than_wals :
    lowestCovered hebrew = .objComparison ∧
    Fragments.Hebrew.relativization.lowestRelativizable = .oblique := by decide

theorem arabic_kc_covers_deeper_than_wals :
    lowestCovered arabic = .objComparison ∧
    Fragments.Arabic.relativization.lowestRelativizable = .oblique := by decide

theorem yoruba_kc_matches_wals :
    lowestCovered yoruba = .genitive ∧
    Fragments.Yoruba.relativization.lowestRelativizable = .genitive := by decide

/-- **Systematic coverage agreement**: K&C is at least as detailed as
    WALS for every sample language. The WALS profile never claims a
    language can relativize a position that K&C Table 1 doesn't cover. -/
theorem kc_at_least_as_detailed_as_wals :
    (lowestCovered english).rank   ≤ Fragments.English.relativization.lowestRelativizable.rank ∧
    (lowestCovered welsh).rank     ≤ Fragments.Welsh.relativization.lowestRelativizable.rank ∧
    (lowestCovered korean).rank    ≤ Fragments.Korean.relativization.lowestRelativizable.rank ∧
    (lowestCovered malagasy).rank  ≤ Fragments.Malagasy.relativization.lowestRelativizable.rank ∧
    (lowestCovered finnish).rank   ≤ Fragments.Finnish.relativization.lowestRelativizable.rank ∧
    (lowestCovered hebrew).rank    ≤ Fragments.Hebrew.relativization.lowestRelativizable.rank ∧
    (lowestCovered arabic).rank    ≤ Fragments.Arabic.relativization.lowestRelativizable.rank ∧
    (lowestCovered yoruba).rank    ≤ Fragments.Yoruba.relativization.lowestRelativizable.rank :=
  by decide

-- ============================================================================
-- § 8: Contiguity Examples (HC₂ instances)
-- ============================================================================

/-! HC₂ ("any RC-forming strategy must apply to a continuous segment of the
AH") is a paper-anchored claim. The contiguity machinery (`contiguousOnAH`,
`AHPosition.rank`) lives in `Core/Relativization/Hierarchy.lean` because it
mirrors `Core/Case/Hierarchy.lean::validInventory` and is genuinely
framework-agnostic. The specific contiguous-segment witnesses below
exemplify HC₂ on the AH and are part of @cite{keenan-comrie-1977}'s core
argumentation. -/

/-- The full hierarchy [SU, DO, IO, OBL, GEN, OCOMP] is contiguous. -/
theorem full_ah_contiguous :
    contiguousOnAH AHPosition.all = true := rfl

/-- A single position is trivially contiguous. -/
theorem singleton_contiguous :
    contiguousOnAH [AHPosition.subject] = true := rfl

/-- [SU, DO] is contiguous. -/
theorem su_do_contiguous :
    contiguousOnAH [AHPosition.subject, .directObject] = true := rfl

/-- [IO, OBL, GEN] is contiguous (a non-primary segment). -/
theorem io_obl_gen_contiguous :
    contiguousOnAH [AHPosition.indirectObject, .oblique, .genitive] = true := rfl

/-- [SU, DO, OBL] is NOT contiguous (skips IO at rank 4). -/
theorem su_do_obl_not_contiguous :
    contiguousOnAH [AHPosition.subject, .directObject, .oblique] = false := rfl

-- ============================================================================
-- § 9: Primary Relativization Constraint (General Proof)
-- ============================================================================

/-! The PRC is the paper's main derivation: it follows from HC₁ + HC₂ rather
than being an independent stipulation. The general proof lives here (paper
content), not in `Core/Relativization/Hierarchy.lean` (substrate). -/

/-- BEq agrees with propositional equality for AH positions. -/
private theorem ah_beq_iff (a b : AHPosition) :
    (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> decide

/-- Nat BEq equality implies propositional equality. -/
private theorem nat_beq_to_eq {n m : Nat} (h : (n == m) = true) : n = m := by
  cases n <;> cases m <;> simp_all [BEq.beq]

/-- If `hasAHRank` finds a position at rank `a.rank`, that position is `a`
    (since rank is injective). -/
private theorem hasAHRank_implies_any
    (positions : List AHPosition) (a : AHPosition)
    (h : hasAHRank positions a.rank = true) :
    positions.any (· == a) = true := by
  unfold hasAHRank at h
  rw [List.any_eq_true] at h ⊢
  obtain ⟨b, hb_mem, hb_rank⟩ := h
  have hrank : b.rank = a.rank := nat_beq_to_eq hb_rank
  have heq : b = a := ah_rank_injective b a hrank
  exact ⟨a, heq ▸ hb_mem, by rw [ah_beq_iff]⟩

/-- If `contiguousOnAH positions = true` and `p1`, `p2` are both in the list
    with `p1.rank < p2.rank`, then every intermediate rank `r` with
    `p1.rank < r < p2.rank` is represented in the list. -/
private theorem contiguous_intermediate
    (positions : List AHPosition)
    (h_contig : contiguousOnAH positions = true)
    (p1 p2 : AHPosition)
    (hp1 : positions.any (· == p1) = true)
    (hp2 : positions.any (· == p2) = true)
    (hlt : p1.rank < p2.rank)
    (r : Nat) (hlo : p1.rank < r) (hhi : r < p2.rank) :
    hasAHRank positions r = true := by
  rw [List.any_eq_true] at hp1 hp2
  obtain ⟨a1, ha1_mem, ha1_eq⟩ := hp1
  obtain ⟨a2, ha2_mem, ha2_eq⟩ := hp2
  rw [ah_beq_iff] at ha1_eq ha2_eq
  have hp1_mem : p1 ∈ positions := ha1_eq ▸ ha1_mem
  have hp2_mem : p2 ∈ positions := ha2_eq ▸ ha2_mem
  unfold contiguousOnAH at h_contig
  rw [List.all_eq_true] at h_contig
  have h1 := h_contig p1 hp1_mem
  rw [List.all_eq_true] at h1
  have h2 := h1 p2 hp2_mem
  simp only [hlt, ↓reduceIte] at h2
  rw [List.all_eq_true] at h2
  have h3 := h2 r (List.mem_range.mpr hhi)
  simp only [hlo, hhi, Bool.and_self] at h3
  exact h3

/-- **Primary Relativization Constraint (general proof).**

    If a list of AH positions is contiguous (HC₂) and contains `.subject`
    (i.e., the strategy is primary), then the list is upward-closed:
    for any covered position `p`, all positions above `p` on the AH
    are also covered.

    This proves that the PRC is a logical consequence of HC₂ + being primary,
    not an independent constraint — the paper's core derivation
    (@cite{keenan-comrie-1977} p. 68: "PRC₂ follows directly from HC₂
    and the definition of primary"). -/
theorem prc_from_hc2 (positions : List AHPosition)
    (h_contig : contiguousOnAH positions = true)
    (h_su : positions.any (· == AHPosition.subject) = true)
    (p above : AHPosition)
    (hp : positions.any (· == p) = true)
    (habove : above.rank > p.rank) :
    positions.any (· == above) = true := by
  by_cases h_eq : above = AHPosition.subject
  · subst h_eq; exact h_su
  · have h_above_lt : above.rank < 6 := by
      cases above <;> simp [AHPosition.rank] at h_eq ⊢
    have h_su_rank : AHPosition.subject.rank = 6 := rfl
    have h_p_lt_su : p.rank < AHPosition.subject.rank := by
      rw [h_su_rank]; omega
    have h_inter := contiguous_intermediate positions h_contig p .subject hp h_su
      h_p_lt_su above.rank habove (by rw [h_su_rank]; omega)
    exact hasAHRank_implies_any positions above h_inter

/-- All 6 canonical primary strategy segments are upward-closed.
    These are the only possible contiguous segments containing `.subject`. -/
theorem prc_all_primary_segments :
    let segs := [
      [AHPosition.subject],
      [.subject, .directObject],
      [.subject, .directObject, .indirectObject],
      [.subject, .directObject, .indirectObject, .oblique],
      [.subject, .directObject, .indirectObject, .oblique, .genitive],
      [.subject, .directObject, .indirectObject, .oblique, .genitive, .objComparison] ]
    segs.all (λ seg =>
      contiguousOnAH seg &&
      seg.any (· == .subject) &&
      seg.all (λ p => AHPosition.all.all (λ above =>
        if above.rank > p.rank then seg.any (· == above) else true))) = true := by
  decide

end Phenomena.Relativization.Studies.KeenanComrie1977
