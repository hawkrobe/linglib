import Linglib.Data.WALS.Features.F49A
import Linglib.Data.WALS.Features.F50A
import Linglib.Data.WALS.Features.F51A
import Linglib.Data.WALS.Features.F52A

/-!
# Case typology — WALS substrate (Chapters 49–52)
@cite{dryer-haspelmath-2013} @cite{iggesen-2013} @cite{stolz-veselinova-2013}

Theory-neutral case-typology substrate distilled from four WALS chapters,
in the same `Linglib/Typology/{Domain}.lean` mould as `WordOrder.lean`,
`Adposition.lean`, etc.:

- **Ch 49** (Iggesen 2013): Number of Cases — five-bin classification of
  morphological case inventory size, plus the `noMorphologicalCaseMarking`
  cell.
- **Ch 50** (Iggesen 2013): Asymmetrical Case-Marking — Iggesen's actual
  five-way WALS partition (`symmetrical`, `additiveQuantitativelyAsymmetrical`,
  `subtractiveQuantitativelyAsymmetrical`, `qualitativelyAsymmetrical`,
  `syncretismInRelevantNpTypes`). Note: an earlier `Phenomena/Case/Typology.lean`
  file silently re-coded this dimension in Aissen-friendly conditioning-factor
  categories (`animacyOnly` / `definitenessOnly` / `pronounOnly` / etc.); that
  re-coding was deleted in the dissolution because (a) it didn't match the
  WALS data the same chapter referenced, (b) it served only a per-language
  hand-curated sample that was itself unsourced, and (c) post-Aissen
  conditioning-factor analyses live in `Studies/Aissen2003.lean` and
  `Features/Prominence.lean::DifferentialMarkingProfile`, not in substrate.
- **Ch 51** (Iggesen 2013): Position of Case Affixes — suffix / prefix /
  tone / mixed.
- **Ch 52** (Stolz & Veselinova 2013): Comitatives & Instrumentals —
  identity vs differentiation vs mixed.

The substrate exposes:
- Enum types per chapter (`CaseCount`, `AsymmetricalCaseMarking`,
  `CaseAffixPosition`, `ComitativeInstrumental`)
- Convenience helpers (`hasDCM`, `hasBoundCase`, `isSyncretic`, etc.)
- Forward maps from the generated WALS feature types to these enums where
  a clean mapping exists (`fromWALS49A`); sparse where Iggesen's WALS bins
  don't align cleanly (Ch 50's WALS-vs-Aissen issue noted above)
- WALS distributional facts proved by `native_decide` over
  `Data.WALS.F{49,50,51,52}A.allData`

No Fragment imports (substrate discipline). Theory-specific apparatus
(Aissen 2003 OT factorial typology, DeHoop-Malchukov BiOT, Grimm 2011
agentivity lattice, Haspelmath 2021 form-frequency correspondences) lives
in `Studies/`. Abstract-case theory (Marantz 1991, Pesetsky
2013, Caha 2009 nanosyntax, Baker 2015 dependent case, Woolford 1997
lexical case) lives in `Linglib/Syntax/Case/` over a different
ontology and does NOT consume this WALS substrate.

-/

set_option autoImplicit false

namespace Typology.Case

private abbrev ch49 := Data.WALS.F49A.allData
private abbrev ch50 := Data.WALS.F50A.allData
private abbrev ch51 := Data.WALS.F51A.allData
private abbrev ch52 := Data.WALS.F52A.allData

-- ============================================================================
-- §1. WALS Ch 49 — Number of Cases
-- ============================================================================

/-- Number-of-cases categories (WALS Ch 49, @cite{iggesen-2013}).

Languages are classified by the number of morphological case distinctions
in their nominal paradigm. WALS additionally distinguishes
`exclusivelyBorderlineCaseMarking` (e.g., English with case only on
pronouns) from the `noMorphologicalCaseMarking` cell, but that distinction
is deliberately not collapsed into a single bin here — see
`fromWALS49A` for the explicit `none` mapping. -/
inductive CaseCount where
  | none      -- no morphological case-marking
  | two       -- exactly 2 cases
  | threeFour -- 3–4 cases
  | fiveSeven -- 5–7 cases
  | eightNine -- 8–9 cases
  | tenPlus   -- 10 or more cases
  deriving DecidableEq, Repr, Inhabited

/-- Numeric lower bound for each `CaseCount` category. -/
def CaseCount.lowerBound : CaseCount → Nat
  | .none      => 0
  | .two       => 2
  | .threeFour => 3
  | .fiveSeven => 5
  | .eightNine => 8
  | .tenPlus   => 10

/-- Whether a raw case count falls in a given `CaseCount` category. -/
def CaseCount.contains (cc : CaseCount) (n : Nat) : Bool :=
  match cc with
  | .none      => n == 0
  | .two       => n == 2
  | .threeFour => n >= 3 && n <= 4
  | .fiveSeven => n >= 5 && n <= 7
  | .eightNine => n >= 8 && n <= 9
  | .tenPlus   => n >= 10

/-- Forward map from the generated WALS Ch 49 type to `CaseCount`.
    Iggesen's `exclusivelyBorderlineCaseMarking` cell (e.g., English with
    case only on pronouns) has no clean mapping into the size-bin scheme
    and returns `Option.none`. -/
def fromWALS49A : Data.WALS.F49A.CaseCount → Option CaseCount
  | .noMorphologicalCaseMarking => some .none
  | .cases2                     => some .two
  | .cases3                     => some .threeFour
  | .cases4                     => some .threeFour
  | .cases5                     => some .fiveSeven
  | .cases6_7                   => some .fiveSeven
  | .cases8_9                   => some .eightNine
  | .cases10OrMore              => some .tenPlus
  | .exclusivelyBorderlineCaseMarking => Option.none

-- ============================================================================
-- §2. WALS Ch 50 — Asymmetrical Case-Marking (Iggesen's actual partition)
-- ============================================================================

/-- WALS Ch 50 (Iggesen 2013): Asymmetrical (differential) case-marking
    typology. **Iggesen's actual five-way classification** — these are
    the categories the WALS data carries. Conditioning-factor analyses
    (animacy / definiteness / pronoun status) are theory-side projections
    over `Features.Prominence.DifferentialMarkingProfile`, not substrate. -/
inductive AsymmetricalCaseMarking where
  /-- Symmetrical: case marking is uniform across NP types. -/
  | symmetrical
  /-- Additive quantitatively asymmetrical: more case distinctions on
      some NP types than others. -/
  | additiveQuantitativelyAsymmetrical
  /-- Subtractive quantitatively asymmetrical: fewer case distinctions
      on some NP types. -/
  | subtractiveQuantitativelyAsymmetrical
  /-- Qualitatively asymmetrical: different markers in the same case
      cell across NP types. -/
  | qualitativelyAsymmetrical
  /-- Syncretism in relevant NP types: case distinctions collapse on
      certain NP types. -/
  | syncretismInRelevantNpTypes
  deriving DecidableEq, Repr, Inhabited

/-- Whether this Ch 50 value indicates any case-marking asymmetry
    (everything other than `symmetrical`). -/
def AsymmetricalCaseMarking.isAsymmetric : AsymmetricalCaseMarking → Bool
  | .symmetrical => false
  | _            => true

/-- Forward map from generated WALS Ch 50 to local enum.
    The WALS source has a `noCaseMarking` cell as well (no morphological
    case at all); we omit it from this enum since asymmetry is
    undefined when there is no case to be asymmetric about. -/
def fromWALS50A : Data.WALS.F50A.AsymmetricalCaseMarking →
    Option AsymmetricalCaseMarking
  | .noCaseMarking                          => Option.none
  | .symmetrical                            => some .symmetrical
  | .additiveQuantitativelyAsymmetrical     => some .additiveQuantitativelyAsymmetrical
  | .subtractiveQuantitativelyAsymmetrical  => some .subtractiveQuantitativelyAsymmetrical
  | .qualitativelyAsymmetrical              => some .qualitativelyAsymmetrical
  | .syncretismInRelevantNpTypes            => some .syncretismInRelevantNpTypes

-- ============================================================================
-- §3. WALS Ch 51 — Position of Case Affixes
-- ============================================================================

/-- Position of case affixes (WALS Ch 51, @cite{iggesen-2013}). -/
inductive CaseAffixPosition where
  | noAffixes         -- no case affixes (no case, or case-by-adposition only)
  | suffixesOnly
  | prefixesOnly
  | toneOnly
  | bothSuffixPrefix
  deriving DecidableEq, Repr, Inhabited

/-- Whether this position type involves bound case morphology. -/
def CaseAffixPosition.hasBoundCase : CaseAffixPosition → Bool
  | .noAffixes => false
  | _          => true

/-- Whether suffixal case marking is present. -/
def CaseAffixPosition.hasSuffix : CaseAffixPosition → Bool
  | .suffixesOnly | .bothSuffixPrefix => true
  | _                                  => false

-- ============================================================================
-- §4. WALS Ch 52 — Comitatives and Instrumentals
-- ============================================================================

/-- Comitative–instrumental relation (WALS Ch 52, @cite{stolz-veselinova-2013}).

In many languages the marker for 'with X' (comitative: accompaniment) and
'by means of X' (instrumental: means/instrument) is the same morpheme
(e.g. Russian instrumental case `-om` ~ `-oj`); other languages distinguish
them (e.g. Japanese `-to` vs `-de`). -/
inductive ComitativeInstrumental where
  | identity        -- same marker for both
  | differentiation -- distinct markers
  | mixed           -- both strategies coexist
  deriving DecidableEq, Repr, Inhabited

/-- Whether the language uses the same morpheme for both functions. -/
def ComitativeInstrumental.isSyncretic : ComitativeInstrumental → Bool
  | .identity => true
  | _         => false

-- ============================================================================
-- §5. WALS chapter sample sizes
-- ============================================================================


/-- Ch 49 and Ch 50 share the same 261-language sample. -/
theorem ch49_ch50_same_sample : ch49.length = ch50.length := by native_decide

-- ============================================================================
-- §6. WALS aggregate distributional facts
-- ============================================================================

/-- Ch 49: Languages with no morphological case-marking are the modal
    category. -/
theorem ch49_no_case_modal :
    let noCases := (ch49.filter (·.value == .noMorphologicalCaseMarking)).length
    noCases > (ch49.filter (·.value == .cases2)).length ∧
    noCases > (ch49.filter (·.value == .cases6_7)).length := by
  exact ⟨by native_decide, by native_decide⟩

/-- Ch 49: Case-bearing languages (any non-zero category) outnumber
    caseless ones. -/
theorem ch49_case_languages_majority :
    let noCases := (ch49.filter (·.value == .noMorphologicalCaseMarking)).length
    ch49.length - noCases > noCases := by native_decide

/-- Ch 50: Languages with some asymmetrical case-marking outnumber
    those with purely symmetrical case. -/
theorem ch50_asymmetry_common :
    let symmetrical := (ch50.filter (·.value == .symmetrical)).length
    let additive := (ch50.filter (·.value == .additiveQuantitativelyAsymmetrical)).length
    let subtractive := (ch50.filter (·.value == .subtractiveQuantitativelyAsymmetrical)).length
    let qualitative := (ch50.filter (·.value == .qualitativelyAsymmetrical)).length
    let syncretism := (ch50.filter (·.value == .syncretismInRelevantNpTypes)).length
    additive + subtractive + qualitative + syncretism > symmetrical := by
  native_decide

/-- Ch 51: Suffixal case is the dominant strategy among case-marking
    languages. -/
theorem ch51_suffix_dominant :
    (ch51.filter (·.value == .caseSuffixes)).length >
    (ch51.filter (·.value == .casePrefixes)).length ∧
    (ch51.filter (·.value == .caseSuffixes)).length >
    (ch51.filter (·.value == .postpositionalClitics)).length := by
  exact ⟨by native_decide, by native_decide⟩

/-- Ch 52: Differentiation is the majority pattern. -/
theorem ch52_differentiation_majority :
    (ch52.filter (·.value == .differentiation)).length >
    (ch52.filter (·.value == .identity)).length ∧
    (ch52.filter (·.value == .differentiation)).length >
    (ch52.filter (·.value == .mixed)).length := by
  exact ⟨by native_decide, by native_decide⟩

end Typology.Case
