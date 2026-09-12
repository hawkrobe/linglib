import Linglib.Data.Examples.Kennedy1999

/-!
# Kennedy (1999): Projecting the Adjective

This file formalizes the judgment data of [kennedy-1999], the dissertation arguing that gradable
adjectives denote measure functions whose relational type is derived by degree morphology, and
that the positive and negative extents of one scale, POSδ and NEGδ of (30) and (31), derive
antonymy and cross-polar anomaly rather than stipulating them. The extent algebra lives in
`Semantics/Degree/Basic.lean`: extents are `Set.Iic (μ x)` and `Set.Ioi (μ x)`, comparison is
extent inclusion (`Degree.comparative_iff_Iic_ssubset`), the antonymy biconditional (54) is
`Degree.antonymy_biconditional`, and cross-polar anomaly (Section 3.1.7) is
`Degree.not_crossExtentInclusion`; the embedding of measure functions into [klein-1980]'s
degree-free delineation semantics is `Degree.delineation_strictly_more_general` in
`Semantics/Degree/Hom.lean`.

The rows of `Data/Examples/Kennedy1999.json` are the cross-polar and incommensurability
comparatives of Sections 3.1.3–3.1.7, with the ficus quadruple (61)–(64) showing the anomaly
reaching beyond antonym pairs, and the measure-phrase constructions of Sections 3.1.8–3.1.9. The
account defines a comparison exactly when the compared extents are of one sort on a shared
scale, and an absolute measure phrase exactly with a positive adjective, whose extents are
bounded; `comparison_defined_iff` and `measurePhrase_positive_iff` check the predicted patterns
against the rows.

## References

* [kennedy-1999]
* [klein-1980]
-/

namespace Kennedy1999

open Data.Examples

/-! ### Cross-polar anomaly (Sections 3.1.3–3.1.7) -/

/-- The two compared adjectives have the same scale polarity. -/
def samePolarity (e : LinguisticExample) : Prop :=
  e.feature? "matrix_polarity" = e.feature? "standard_polarity"

instance (e : LinguisticExample) : Decidable (samePolarity e) :=
  inferInstanceAs (Decidable (_ = _))

/-- The two compared adjectives project onto a shared scale. -/
def sharedScale (e : LinguisticExample) : Prop :=
  e.feature? "shared_scale" = some "true"

instance (e : LinguisticExample) : Decidable (sharedScale e) :=
  inferInstanceAs (Decidable (_ = _))

/-- The subdeletion comparatives: cross-polar anomalies, same-polarity controls, the ficus
quadruple, and the incommensurability cases. -/
def crossPolarRows : List LinguisticExample :=
  [ Examples.cpa_long_short, Examples.cpa_short_long
  , Examples.subdel_pos_pos, Examples.subdel_neg_neg
  , Examples.ficus_tall_high, Examples.ficus_tall_low
  , Examples.ficus_short_low, Examples.ficus_short_high
  , Examples.incomm_tall_clever, Examples.incomm_tragic_heavy ]

/-- A subdeletion comparative is acceptable exactly when the compared extents are of the same
sort on a shared scale: cross-polar anomaly and incommensurability under one condition, the
polarity half of which is `Degree.not_crossExtentInclusion`. -/
theorem comparison_defined_iff :
    ∀ e ∈ crossPolarRows, e.judgment = .acceptable ↔ (samePolarity e ∧ sharedScale e) := by
  decide

/-! ### Measure phrases (Sections 3.1.8–3.1.9)

Measure phrases denote bounded extents. On a scale with a minimum the positive extents are
bounded and the negative ones are not, so an absolute construction composing a measure phrase
with a negative adjective is undefined, (69) *My Cadillac is 8 feet long* against (70) *My Fiat
is 5 feet short*; the phrasal comparative (73) *My Fiat is shorter than 8 feet* is the contrast,
its standard derived by applying the adjective to the measure phrase. -/

/-- The absolute measure-phrase constructions. -/
def measurePhraseAbsoluteRows : List LinguisticExample :=
  [ Examples.mp_cadillac, Examples.mp_fiat, Examples.mp_reich, Examples.mp_slow ]

/-- An absolute measure-phrase construction is acceptable exactly with a positive adjective,
whose extents are bounded. -/
theorem measurePhrase_positive_iff :
    ∀ e ∈ measurePhraseAbsoluteRows,
      e.judgment = .acceptable ↔ e.feature? "polarity" = some "positive" := by
  decide

end Kennedy1999
