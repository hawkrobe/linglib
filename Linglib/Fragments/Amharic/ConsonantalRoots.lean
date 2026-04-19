import Linglib.Core.Morphology.ConsonantalRoot
import Linglib.Theories.Phonology.OptimalityTheory.Constraints

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
    @cite{broselow-1984} analyzes this as a *biradical* √fd with /t/
    as a default consonant inserted to satisfy the template;
    @cite{faust-2026} reanalyzes it as triradical with the third
    radical /j/, which palatalizes the preceding [d] to [dʒ] in the
    verbal paradigm and fails to surface as a separate segment. In
    nominal forms (gerund, INF), the feminine /t/ intrudes — *not* as
    a default consonant but as the n[+gen] exponent (@cite{faust-2026}
    (7)–(8), (11)–(12)). -/
def fdj : Root String := ⟨["f", "d", "j"]⟩

/-- √hid — base of [hed-ä] `go` PFV.3MSG, INF [mäh(i)d].
    A "hollow" root in the standard analysis: the medial radical /i/
    is non-consonantal and merges with the vocalization
    (@cite{faust-2026} (12e), (13c)). -/
def hid : Root String := ⟨["h", "i", "d"]⟩

/-- √sma — base of [sämm-a] `hear` PFV.3MSG, INF [mäsmat]
    (@cite{faust-2026} (12c), (13a)). The non-consonantal final radical
    /a/ merges with the vocalization. -/
def sma : Root String := ⟨["s", "m", "a"]⟩

/-- √sam — base of [sam-ä] `kiss` PFV.3MSG, INF [mäsam]
    (@cite{faust-2026} (12d), (13b)). The non-consonantal medial
    radical /a/ merges with the vocalization. -/
def sam : Root String := ⟨["s", "a", "m"]⟩

-- ============================================================================
-- § 2: True triradical (control) and Faust's biradical reanalysis
-- ============================================================================

/-- √sbr — base of [säbbär-ä] `break` PFV.3MSG, INF [mäsbär]
    (@cite{faust-2026} (5a), (12a)). A canonical type-A triradical
    with three distinct surface consonants. -/
def sbr : Root String := ⟨["s", "b", "r"]⟩

/-- √wd — base of [wäddäd-ä] `liked` PFV.3MSG (@cite{faust-2026} (5b),
    page 432). Both @cite{broselow-1984} and @cite{faust-2026} agree
    this is a *biradical* root. The two analysts diverge on √fdj
    (Broselow: biradical √fd; Faust: triradical √fdj) but agree on
    √wd. Crucially for @cite{faust-2026}: √wd does *not* violate the
    OCP at the root level, since /w/ ≠ /d/ — even though it surfaces
    with adjacent identical [d][d] in [wäddäd-ä]. The surface gemination
    is a template-spreading effect, not a root-level identity. -/
def wd : Root String := ⟨["w", "d"]⟩

-- ============================================================================
-- § 3: Sanity properties
-- ============================================================================

theorem fdj_triradical : fdj.triradical = true := rfl
theorem sbr_triradical : sbr.triradical = true := rfl
theorem wd_biradical : wd.biradical = true := rfl

/-- @cite{faust-2026}'s key claim about √wd (page 432): even though
    the surface form [wäddäd-ä] has adjacent identical [d][d], the
    *root* √wd has no adjacent identical segments — so the OCP is
    not violated at the root level. The biradical analysis (shared
    with @cite{broselow-1984}) is therefore maintained. -/
theorem wd_no_adjacent_identical :
    Phonology.Constraints.adjacentIdentical wd.segments = 0 := rfl

end Fragments.Amharic
