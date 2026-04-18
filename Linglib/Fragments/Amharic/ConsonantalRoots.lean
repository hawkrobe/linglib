import Linglib.Core.Morphology.ConsonantalRoot

/-!
# Amharic Consonantal Roots

A minimal inventory of Amharic verbal roots used by @cite{faust-2026}'s
re-analysis of @cite{broselow-1984}'s claim that Amharic admits OCP-violating
biradical roots like √TT/√QQ.

@cite{faust-2026} argues that the seemingly-biconsonantal verbs (paradigm
(5b), e.g. [wäddäd-ä] `liked`) are in fact triradical √wdd, satisfying the
template by spreading; while the [t]-intruding paradigm (5c)/(12)/(13) is
triradical with a [j] in the final position whose palatality merges with
the preceding consonant — under this analysis Amharic has no OCP-violating
roots after all.
-/

namespace Fragments.Amharic

open Core.Morphology

-- ============================================================================
-- § 1: [j]-final triradicals — the [t]-intrusion class (@cite{faust-2026} (5c))
-- ============================================================================

/-- √fdj — base of [fädʤ-ä] `scorch` PFV.3MSG, [fädʤ-o] gerund.
    The final [j] palatalizes the preceding [d] to [dʒ] in the verbal
    paradigm and fails to surface as a separate segment. In nominal
    forms (gerund, INF), [t] intrudes to satisfy the template
    (@cite{faust-2026} (8)). -/
def fdj : Root String := ⟨["f", "d", "j"]⟩

/-- √hid — base of [hed-ä] `go` PFV.3MSG. A "hollow" root in the
    standard analysis (@cite{faust-2026} (12e), (13c)). -/
def hid : Root String := ⟨["h", "i", "d"]⟩

/-- √sma — base of [sämm-a] `hear` PFV.3MSG (@cite{faust-2026} (12c)). -/
def sma : Root String := ⟨["s", "m", "a"]⟩

/-- √sam — base of [sam-ä] `kiss` PFV.3MSG (@cite{faust-2026} (12d), (13b)). -/
def sam : Root String := ⟨["s", "a", "m"]⟩

-- ============================================================================
-- § 2: True triradical (control) and apparent biradical
-- ============================================================================

/-- √sbr — base of [säbbär-ä] `break` PFV.3MSG (@cite{faust-2026} (5a)).
    A canonical type-A triradical with three distinct surface consonants. -/
def sbr : Root String := ⟨["s", "b", "r"]⟩

/-- √wdd — Faust's re-analysis of [wäddäd-ä] `liked` PFV.3MSG
    (@cite{faust-2026} (5b)). Broselow analyzes this as biradical
    OCP-violating √wd; Faust analyzes it as triradical with identical
    final radicals, satisfying the OCP at the root level. -/
def wdd : Root String := ⟨["w", "d", "d"]⟩

-- ============================================================================
-- § 3: Sanity properties
-- ============================================================================

theorem fdj_triradical : fdj.triradical = true := rfl
theorem sbr_triradical : sbr.triradical = true := rfl
theorem wdd_triradical : wdd.triradical = true := rfl

/-- @cite{faust-2026}'s key empirical claim: under his analysis,
    [wäddäd-ä] is based on a triradical √wdd, not a biradical √wd. -/
theorem wdd_is_not_biradical : wdd.biradical = false := rfl

end Fragments.Amharic
