import Linglib.Data.Examples.Kennedy1999
import Linglib.Syntax.Category.Degree.Basic

/-!
# Kennedy 1999: Projecting the Adjective

Study file for [kennedy-1999], the dissertation arguing that gradable
adjectives denote measure functions (⟦tall⟧ = λx. height(x)) whose relational
⟨d,⟨e,t⟩⟩ type is derived by degree morphology, and that positive and negative
*extents* of the same scale (POSδ and NEGδ, eqs (30)–(31)) derive antonymy and
cross-polar anomaly rather than stipulating them. The extent algebra is
formalised in `Semantics/Degree/Basic.lean`: extents are `Set.Iic (μ x)` /
`Set.Ioi (μ x)`, comparison is extent inclusion
(`Degree.comparative_iff_Iic_ssubset`), the antonymy biconditional (54) is
`Degree.antonymy_biconditional`, and cross-polar anomaly (§3.1.7) is
`Degree.not_crossExtentInclusion`. The embedding of measure functions into
[klein-1980]'s rival degree-free delineation semantics is in
`Semantics/Degree/Hom.lean` (`Degree.delineation_strictly_more_general`).

The judgment data live in `Data/Examples/Kennedy1999.json`: the cross-polar
and incommensurability comparatives of §3.1.3–§3.1.7 (including the ficus
quadruple (61)–(64) showing the anomaly generalizes beyond antonym pairs) and
the measure-phrase restriction of §3.1.8–§3.1.9. Kennedy's account defines
comparison exactly when the compared extents are of the same sort on a shared
scale; `comparison_defined_iff` and `measurePhrase_positive_iff` check the
predicted judgment patterns row by row.
-/

namespace Kennedy1999

open Data.Examples (LinguisticExample)

/-! ### Cross-polar anomaly (§3.1.3–§3.1.7) -/

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

/-- The subdeletion comparatives of §3.1.3–§3.1.7: cross-polar anomalies,
same-polarity controls, the ficus quadruple, and the incommensurability
cases. -/
def crossPolarRows : List LinguisticExample :=
  [ Examples.cpa_long_short, Examples.cpa_short_long
  , Examples.subdel_pos_pos, Examples.subdel_neg_neg
  , Examples.ficus_tall_high, Examples.ficus_tall_low
  , Examples.ficus_short_low, Examples.ficus_short_high
  , Examples.incomm_tall_clever, Examples.incomm_tragic_heavy ]

/-- A subdeletion comparative is acceptable exactly when the compared extents
are of the same sort on a shared scale — sortal cross-polar anomaly and
incommensurability under one condition. `Degree.not_crossExtentInclusion` is
the lattice-algebraic shadow of the polarity half. -/
theorem comparison_defined_iff :
    ∀ e ∈ crossPolarRows,
      e.judgment = .acceptable ↔ (samePolarity e ∧ sharedScale e) := by
  decide

/-! ### Measure phrase distribution (§3.1.8–§3.1.9)

Measure phrases denote bounded extents. On a scale with a minimum, positive
extents are bounded but negative extents are not, so an absolute construction
composing a measure phrase with a negative adjective is undefined — (69) "My
Cadillac is 8 feet long" vs (70) "#My Fiat is 5 feet short". The phrasal
comparative (73) "My fiat is shorter than 8 feet" is the paper's contrast:
there the standard is derived by applying the adjective to the measure
phrase. -/

/-- The absolute measure-phrase constructions of §3.1.8–§3.1.9. -/
def measurePhraseAbsoluteRows : List LinguisticExample :=
  [ Examples.mp_cadillac, Examples.mp_fiat
  , Examples.mp_reich, Examples.mp_slow ]

/-- An absolute measure-phrase construction is acceptable exactly with a
positive adjective, whose extents are bounded. -/
theorem measurePhrase_positive_iff :
    ∀ e ∈ measurePhraseAbsoluteRows,
      e.judgment = .acceptable ↔ e.feature? "polarity" = some "positive" := by
  decide

/-! ### DegP projection

Degree morphemes are functional heads taking AdjP as complement:
`[DegP [Deg° -er, as, -est, too, enough] [AdjP tall]]` (ch. 2, the extended
projection of A). The head inventory is `Degree.Head`. -/

/-- A degree head with its adjective complement. -/
structure HistoricalDegP where
  head : Degree.Head
  adjective : String
  deriving Repr

/-- DegP constructions from the paper. -/
def exampleDegPs : List HistoricalDegP :=
  [ { head := .comparative, adjective := "tall" }    -- "taller"
  , { head := .equative, adjective := "tall" }       -- "as tall"
  , { head := .superlative, adjective := "tall" }    -- "tallest"
  , { head := .excessive, adjective := "expensive" } -- "too expensive"
  , { head := .sufficiency, adjective := "old" }     -- "old enough"
  ]

end Kennedy1999
