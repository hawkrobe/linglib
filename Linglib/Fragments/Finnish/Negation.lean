import Linglib.Morphology.Periphrasis
import Linglib.Morphology.Realization
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

open Morphology (MorphCategory MorphRule InflDistribution)
open Syntax.Negation

/-! ### Marker and system -/

/-- *ei* — Finnish's negative auxiliary verb, cited in 3sg form.
    Genuine auxiliary: inflects for person and number (`negParadigm` below
    has the 6 present-tense forms) and bears the agreement and tense
    markers that the lexical verb would otherwise carry. The lexical verb
    appears in the connegative form (`connegativeRule`). The 6 surface
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

/-- The connegative `MorphRule`: strips tense marking from the main verb,
    leaving only the bare stem. The negative auxiliary carries tense instead.

    Example: *mene-n* (I go) → *en mene* (I don't go)
    - neg aux *en* carries 1sg agreement
    - main verb *mene* is the connegative (bare stem) -/
def connegativeRule : MorphRule Bool :=
  { category := .negation
  , value := "connegative"
  , formRule := id  -- connegative = bare stem (tense suffix removed)
  , featureRule := fun f => { f with tense := none }
  , semEffect := not  -- negation flips truth value
  , delegatedSemantics := false }

/-- The negative auxiliary's agreement rule: semantically vacuous,
    carries person/number agreement that would otherwise be on the main verb. -/
def negAgreementRule (person : Nat) (number : String) : MorphRule Bool :=
  { category := .agreement .subj
  , value := s!"{person}{number}"
  , formRule := fun _ =>
    match person, number with
    | 1, "sg" => "en"  | 2, "sg" => "et"  | 3, "sg" => "ei"
    | 1, "pl" => "emme" | 2, "pl" => "ette" | 3, "pl" => "eivät"
    | _, _ => "ei"
  , featureRule := fun f => { f with person := some (if person == 1 then .first
      else if person == 2 then .second else .third) }
  , semEffect := id
  , delegatedSemantics := true }

/-! ### Inflection distribution -/

/-- Finnish negative construction inflection distribution.

    The negative auxiliary hosts: negation, tense, agreement.
    The main verb retains: stem, aspect (via participle choice).
    Uses the shared `InflDistribution` from `Morphology`:
    `onAux` = negative auxiliary, `onLex` = main verb. -/
def finnishNegDistribution : InflDistribution :=
  { onAux := [.negation, .tense, .agreement .subj]
  , onLex := [.stem, .aspect] }

/-! ### Verification -/

/-- The paradigm has exactly 6 forms (3 persons × 2 numbers). -/
theorem paradigm_size : negParadigm.length = 6 := by decide

/-- The connegative rule's semantic effect is Boolean negation. -/
theorem connegative_negates : connegativeRule.semEffect true = false := rfl

/-- Negation (rank 7) hosts agreement (rank 8) on the negative auxiliary —
    respecting Bybee's hierarchy within the neg aux word. -/
theorem neg_aux_respects_bybee :
    MorphCategory.RelevanceLT .negation (.agreement .subj) := by decide

end Finnish.Negation
