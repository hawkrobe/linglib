import Linglib.Syntax.Negation
import Linglib.Fragments.English.Negation
import Linglib.Fragments.German.Negation
import Linglib.Fragments.Romance.French.Negation
import Linglib.Fragments.Slavic.Russian.Negation
import Linglib.Fragments.Finnish.Negation
import Linglib.Fragments.Japanese.Negation
import Linglib.Fragments.Mandarin.Negation
import Linglib.Fragments.Turkish.Negation
import Linglib.Fragments.Slavic.Czech.Negation
import Linglib.Fragments.Spanish.Negation
import Linglib.Fragments.Italian.Negation
import Linglib.Fragments.Burmese.Negation
import Linglib.Fragments.Maori.Negation
import Linglib.Fragments.Hixkaryana.Negation
import Linglib.Fragments.Quechua.Negation

/-!
# Dryer (2013): WALS chapters on negation morpheme + word-order (112A, 143A, 144A)
[dryer-2013-wals] [wals-2013]

WALS chapters by Matthew S. Dryer covering negation typology:

- Ch 112A: Negative Morphemes
- Ch 143A: Order of Negative Morpheme and Verb
- Ch 144A: Position of Negative Word with Respect to Subject, Object, Verb

Per the project's "WALS goes to `Linglib/Typology/`" rule, the WALS aggregate
distributions live in the substrate (`Linglib/Typology/Negation.lean`). This
study file holds **cross-linguistic generalisations** that consume the
Fragment-side `negationProfile` data with non-trivial semantic content
(`bipartite_implies_asymmetric`, `aux_verb_implies_afin`, etc.).

Per-language Fragment-vs-WALS data-equality theorems are **deliberately
absent**: `Fragments.{Lang}.Negation.negationProfile` already encodes the
typed value at definition site, and verifying it equals
`Data.WALS.lookup "iso"` is "encoding conclusions as definitions" — the
two would have to diverge for the theorem to fail, and the substrate's
`NegationSystem.ofISO` already populates from the same WALS source.

Ch 113-115 (Miestamo's symmetric/asymmetric chapters) are grounded in
`Studies/Miestamo2005.lean`.
-/

set_option autoImplicit false

namespace Dryer2013Negation

open Syntax.Negation

-- ============================================================================
-- §1. The 15-language Fragment sample
-- ============================================================================

/-- The 15-language sample drawn from per-language Fragment Negation files.
    Sample shrunk from the dissolved file's 19 (dropped Izi, KolymaYukaghir,
    Rama, Nelemwa — none of which had Fragment files in the project). -/
def allLanguages : List NegationProfile :=
  [ English.Negation.negationProfile
  , German.Negation.negationProfile
  , French.Negation.negationProfile
  , Russian.Negation.negationProfile
  , Finnish.Negation.negationProfile
  , Japanese.Negation.negationProfile
  , Mandarin.Negation.negationProfile
  , Turkish.Negation.negationProfile
  , Czech.Negation.negationProfile
  , Spanish.Negation.negationProfile
  , Italian.Negation.negationProfile
  , Burmese.Negation.negationProfile
  , Maori.Negation.negationProfile
  , Hixkaryana.Negation.negationProfile
  , Quechua.Negation.negationProfile ]

-- ============================================================================
-- §2. Sample-level distributions
-- ============================================================================

/-- Sample size. -/
theorem sample_size : allLanguages.length = 15 := by native_decide

/-- Morpheme type distribution in the sample. -/
theorem sample_affix_count : countByMorphemeType allLanguages .affix = 4 := by
  native_decide
theorem sample_particle_count :
    countByMorphemeType allLanguages .particle = 8 := by native_decide
theorem sample_auxverb_count :
    countByMorphemeType allLanguages .auxVerb = 1 := by native_decide
theorem sample_double_count :
    countByMorphemeType allLanguages .doubleNeg = 1 := by native_decide
theorem sample_unclear_count :
    countByMorphemeType allLanguages .wordUnclear = 1 := by native_decide
theorem sample_variation_count :
    countByMorphemeType allLanguages .variation = 0 := by native_decide

/-- Symmetry distribution in the sample. -/
theorem sample_symmetry_counts :
    countBySymmetry allLanguages .symmetric = 6 ∧
    countBySymmetry allLanguages .asymmetric = 5 ∧
    countBySymmetry allLanguages .both = 4 := by
  native_decide

-- ============================================================================
-- §3. Cross-linguistic generalisations
-- ============================================================================

/-- In the sample, every language with bipartite ("double") negation
    morphemes has asymmetric negation. If negation requires two markers
    whose placement changes the clause structure, the negative clause
    structurally differs from the affirmative. -/
theorem bipartite_implies_asymmetric :
    let bipartite := allLanguages.filter (·.hasMorphemeType .doubleNeg)
    bipartite.all (·.hasAsymmetric) = true := by
  native_decide

/-- In the sample, every language classified as symmetric-only (Ch 113)
    has a non-assignable asymmetry subtype (Ch 114). -/
theorem symmetric_implies_nonassignable :
    let symmetric := allLanguages.filter (·.symmetry == .symmetric)
    symmetric.all (·.asymmetrySubtype == .nonAssignable) = true := by
  native_decide

/-- In the sample, no language classified as asymmetric or both has a
    non-assignable subtype. -/
theorem asymmetric_implies_assignable :
    let asymmetric := allLanguages.filter (·.hasAsymmetric)
    asymmetric.all (·.asymmetrySubtype != .nonAssignable) = true := by
  native_decide

/-- Negative auxiliary verbs (Ch 112) are always associated with asymmetric
    negation of subtype A/Fin: the auxiliary becomes the finite element, and
    the lexical verb is deficitized. Finnish illustrates this perfectly. -/
theorem aux_verb_implies_afin :
    let auxLangs := allLanguages.filter (·.hasMorphemeType .auxVerb)
    auxLangs.all (·.asymmetrySubtype == .finiteness) = true := by
  native_decide

/-- All Slavic languages in the sample (Russian, Czech) show negative concord. -/
theorem slavic_neg_concord :
    Russian.Negation.negationProfile.hasNegConcord = true ∧
    Czech.Negation.negationProfile.hasNegConcord = true := by
  exact ⟨by native_decide, by native_decide⟩

end Dryer2013Negation
