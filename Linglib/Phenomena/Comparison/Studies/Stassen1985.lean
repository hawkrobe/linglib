import Linglib.Phenomena.Comparison.Typology
import Linglib.Phenomena.ClauseChaining.Data
import Linglib.Core.Case.ComparativeEntry
import Linglib.Fragments.Japanese.Comparison
import Linglib.Fragments.Korean.Comparison
import Linglib.Fragments.Turkish.Comparison

/-!
# Stassen 1985: Comparison and Universal Grammar
@cite{stassen-1985}

Stassen's central explanatory claim is that comparative construction types
are **predicted by** a language's temporal clause chaining strategy. The
link runs through a diachronic pathway: comparatives develop from temporal
constructions ("X is tall; Y is not tall" → "X is taller than Y"), and
the type of temporal construction available determines which comparative
type emerges.

This study file connects two phenomenon directories — `Comparison/Typology`
and `ClauseChaining/Data` — proving that the languages in our sample
satisfy Stassen's chaining universals where testable.

## Chaining universals (Stassen 1985, Ch 8)

The key universals connect clause-linking strategy to comparative type:

1. **Deranking universal**: Languages that derank medial verbs (reduce TAM
   morphology) tend to develop locational (separative/allative/locative)
   comparatives.

2. **Balancing universal**: Languages that balance medial verbs (retain full
   morphology) tend to develop conjoined or particle comparatives.

3. **No-SR corollary**: Languages without switch-reference that use converbal
   clause chaining (Korean, Turkish, Japanese) develop separative comparatives
   — the medial verb's reduced morphology correlates with spatial case marking
   on the standard NP.

## Fragment bridge theorems

We also verify that the `ComparativeEntry` data in `Fragments/` is consistent
with the typological classifications in `Comparison/Typology`. This connects
the three layers: Fragments (lexical data) ↔ Phenomena/Comparison (typology)
↔ Phenomena/ClauseChaining (chaining parameters).
-/

namespace Phenomena.Comparison.Studies.Stassen1985

open Phenomena.Comparison.Typology

-- ════════════════════════════════════════════════════
-- § 1. Deranking Universal
-- ════════════════════════════════════════════════════

/-- A clause chaining language "deranks" medial verbs if at least two TAM
    categories are absent or restricted. This is a simplified operationalization
    of Stassen's deranking concept. -/
def isDeranking (p : Phenomena.ClauseChaining.Typology.ClauseChainingParams) : Bool :=
  let count := [p.medialMorph.tense, p.medialMorph.agreement,
                p.medialMorph.mood, p.medialMorph.aspect].filter
    (· != Phenomena.ClauseChaining.Typology.CategoryRetention.full) |>.length
  count ≥ 2

/-- All six clause chaining languages in our sample are deranking.
    This is expected: converbal constructions characteristically reduce
    TAM morphology on the dependent verb. -/
theorem all_sample_deranking :
    Phenomena.ClauseChaining.Data.allLanguages.all (isDeranking ·) = true := by native_decide

-- ════════════════════════════════════════════════════
-- § 2. Deranking → Locational (for no-SR languages)
-- ════════════════════════════════════════════════════

/-- The no-SR clause chaining languages in the chaining sample. -/
def noSRChainingLanguages :
    List Phenomena.ClauseChaining.Typology.ClauseChainingParams :=
  Phenomena.ClauseChaining.Data.allLanguages.filter (! ·.hasSR)

/-- There are exactly 2 no-SR languages in the chaining sample:
    Korean and Turkish. -/
theorem noSR_count : noSRChainingLanguages.length = 2 := by native_decide

/-- The no-SR chaining languages in our sample (Korean, Turkish) both have
    locational comparatives, as Stassen's deranking universal predicts.
    Japanese is also a separative comparative language with no SR, but is
    not in the chaining sample (it would behave identically). -/
theorem korean_locational :
    korean.comparativeType = .locational := rfl

theorem turkish_locational :
    turkish.comparativeType = .locational := rfl

/-- Both no-SR chaining languages have separative (ablative) comparatives
    at the finer 1985 level. -/
theorem korean_separative : korean1985 = .separative := rfl
theorem turkish_separative : turkish1985 = .separative := rfl

-- ════════════════════════════════════════════════════
-- § 3. Localistic Hypothesis: Spatial Case → Comparative Marker
-- ════════════════════════════════════════════════════

/-- The localistic hypothesis: separative comparatives use ablative spatial
    case markers. The spatial case function returns `.abl` for separative. -/
theorem separative_uses_ablative :
    ComparativeType1985.separative.spatialCase = some .abl := rfl

theorem allative_uses_allative :
    ComparativeType1985.allative.spatialCase = some .all := rfl

theorem locative_uses_locative :
    ComparativeType1985.locative.spatialCase = some .loc := rfl

/-- Non-spatial comparative types (exceed, conjoined, particle) have no
    spatial case — their standard markers are not spatial in origin. -/
theorem exceed_no_spatial :
    ComparativeType1985.exceed.spatialCase = none := rfl

theorem conjoined_no_spatial :
    ComparativeType1985.conjoined.spatialCase = none := rfl

theorem particle_no_spatial :
    ComparativeType1985.particle.spatialCase = none := rfl

-- ════════════════════════════════════════════════════
-- § 4. Fragment Bridge: ComparativeEntry ↔ Typology
-- ════════════════════════════════════════════════════

/-- Japanese Fragment entry's standard case matches the 1985 type's
    predicted spatial case. -/
theorem japanese_fragment_case_matches_1985 :
    some Fragments.Japanese.Comparison.entry.standardCase =
    japanese1985.spatialCase := rfl

/-- Korean Fragment entry's standard case matches the 1985 type's
    predicted spatial case. -/
theorem korean_fragment_case_matches_1985 :
    some Fragments.Korean.Comparison.entry.standardCase =
    korean1985.spatialCase := rfl

/-- Turkish Fragment entry's standard case matches the 1985 type's
    predicted spatial case. -/
theorem turkish_fragment_case_matches_1985 :
    some Fragments.Turkish.Comparison.entry.standardCase =
    turkish1985.spatialCase := rfl

/-- Japanese Fragment entry's standard marker matches the Typology profile. -/
theorem japanese_marker_matches_typology :
    Fragments.Japanese.Comparison.entry.standardMarker =
    japanese.standardMarker := rfl

/-- Korean Fragment entry's standard marker matches the Typology profile. -/
theorem korean_marker_matches_typology :
    Fragments.Korean.Comparison.entry.standardMarker =
    korean.standardMarker := rfl

/-- All three Fragment entries agree on case assignment: fixed. -/
theorem all_separative_fixed_case :
    Fragments.Japanese.Comparison.entry.caseAssignment = .fixed ∧
    Fragments.Korean.Comparison.entry.caseAssignment = .fixed ∧
    Fragments.Turkish.Comparison.entry.caseAssignment = .fixed :=
  ⟨rfl, rfl, rfl⟩

/-- All three Fragment entries agree on encoding: adverbial. -/
theorem all_separative_adverbial :
    Fragments.Japanese.Comparison.entry.fixedEncoding = some .adverbial ∧
    Fragments.Korean.Comparison.entry.fixedEncoding = some .adverbial ∧
    Fragments.Turkish.Comparison.entry.fixedEncoding = some .adverbial :=
  ⟨rfl, rfl, rfl⟩

/-- None of the three separative languages have degree morphology, consistent
    with Stassen's observation that separative comparatives typically lack
    overt comparative marking on the adjective. -/
theorem separative_no_degree_morphology :
    Fragments.Japanese.Comparison.entry.hasDegreeMorphology = false ∧
    Fragments.Korean.Comparison.entry.hasDegreeMorphology = false ∧
    Fragments.Turkish.Comparison.entry.hasDegreeMorphology = false :=
  ⟨rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════
-- § 5. Three-Layer Consistency
-- ════════════════════════════════════════════════════

/-- Three-layer consistency for Japanese: Fragment (ablative case) ↔
    Typology (locational/separative) ↔ ClauseChaining (no SR, deranking).

    The Fragment says the standard case is ablative. The Typology says
    Japanese is separative (which maps to locational). The 1985 type
    predicts ablative spatial case. All three agree. -/
theorem japanese_three_layer :
    -- Fragment → 1985 type spatial case
    some Fragments.Japanese.Comparison.entry.standardCase =
      japanese1985.spatialCase ∧
    -- 1985 type → WALS type
    japanese1985.toWALS = Typology.japanese.comparativeType ∧
    -- 1985 type is separative
    japanese1985 = .separative :=
  ⟨rfl, rfl, rfl⟩

/-- Three-layer consistency for Korean. -/
theorem korean_three_layer :
    some Fragments.Korean.Comparison.entry.standardCase =
      korean1985.spatialCase ∧
    korean1985.toWALS = Typology.korean.comparativeType ∧
    korean1985 = .separative :=
  ⟨rfl, rfl, rfl⟩

/-- Three-layer consistency for Turkish. -/
theorem turkish_three_layer :
    some Fragments.Turkish.Comparison.entry.standardCase =
      turkish1985.spatialCase ∧
    turkish1985.toWALS = Typology.turkish.comparativeType ∧
    turkish1985 = .separative :=
  ⟨rfl, rfl, rfl⟩

end Phenomena.Comparison.Studies.Stassen1985
