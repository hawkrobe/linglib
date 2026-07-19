import Linglib.Morphology.Morphotactics.RelevanceHierarchy
import Linglib.Syntax.Negation

/-!
# Finnish Negation: The Negative Auxiliary *ei* [karlsson-2017]
[bybee-1985] [miestamo-2005] [haspelmath-2013]

Finnish expresses sentential negation through a **conjugated negative
auxiliary verb** *ei*. The negative verb inflects
for person and number, while the lexical verb appears in a nonfinite
**connegative** form that lacks tense/agreement marking.

## Paradigm (present indicative)

| Person | Sg      | Pl       |
|--------|---------|----------|
| 1      | e-n     | e-mme    |
| 2      | e-t     | e-tte    |
| 3      | e-i     | e-ivät   |

## Key structural property

The negative auxiliary bears the inflection that the main verb would
otherwise carry. This splits the [bybee-1985] relevance hierarchy:
negation (rank 7) hosts agreement (rank 8) and tense, while the
main verb retains only the stem and aspect. This is a counter-example
to strict stem-outward ordering within a single word — the ordering
principle holds across the analytical construction (neg aux + main verb)
rather than within a synthetic word.

-/

namespace Finnish.Negation

open Morphology (MorphCategory)
open Syntax.Negation

/-! ### Marker and system -/

/-- *ei* — Finnish's negative auxiliary verb, cited in 3sg form.
    Genuine auxiliary: inflects for person and number (`negParadigm` below
    has the 6 present-tense forms) and bears the agreement and tense
    markers that the lexical verb would otherwise carry. The lexical verb
    appears in the connegative form (tense-stripped: *e-n osta* 'I don't
    buy' loses the tense marking *osta-n* 'I buy' carries). The 6 surface
    forms (en/et/ei/emme/ette/eivät) are accessible via `negParadigm`. -/
def ei : NegMarkerEntry :=
  { form := "ei"
  , morphemeType := .auxVerb
  , position := .preverbal }

/-- The Finnish negation system: a single negative auxiliary with a
    person/number paradigm. Multiple paradigm-form *surface* realizations
    (`negParadigm`) are not multiple *markers* — they're inflectional
    variants of one auxiliary, captured cross-linguistically by the single
    `NegMarkerEntry`. The Fragment-side joint consumed by
    `Studies/Dryer2013Negation.lean`. -/
def negationSystem : NegationSystem :=
  NegationSystem.ofISO "fin" [ei]

/-! ### Negative auxiliary paradigm -/

/-- Person–number features for the Finnish negative auxiliary. -/
structure NegForm where
  person : Nat  -- 1, 2, or 3
  number : String  -- "sg" or "pl"
  form : String  -- the surface form
  deriving Repr, BEq

/-- Full present-tense paradigm of the negative auxiliary *ei*. -/
def negParadigm : List NegForm :=
  [ ⟨1, "sg", "en"⟩
  , ⟨2, "sg", "et"⟩
  , ⟨3, "sg", "ei"⟩
  , ⟨1, "pl", "emme"⟩
  , ⟨2, "pl", "ette"⟩
  , ⟨3, "pl", "eivät"⟩ ]

/-! ### Connegative formation -/

/-! ### Inflection distribution -/


/-! ### Verification -/

/-- The paradigm has exactly 6 forms (3 persons × 2 numbers). -/
theorem paradigm_size : negParadigm.length = 6 := by decide

theorem neg_aux_respects_bybee :
    MorphCategory.RelevanceLT .negation (.agreement .subj) := by decide

end Finnish.Negation
