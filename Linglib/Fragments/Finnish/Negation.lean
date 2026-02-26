import Linglib.Core.Lexical.MorphRule
import Linglib.Core.Lexical.Word

/-!
# Finnish Negation: The Negative Auxiliary *ei* @cite{karlsson-2018}

Finnish expresses sentential negation through a **conjugated negative
auxiliary verb** *ei* (Karlsson 2018, Ch. 11). The negative verb inflects
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
otherwise carry. This splits the Bybee (1985) relevance hierarchy:
negation (rank 7) hosts agreement (rank 8) and tense, while the
main verb retains only the stem and aspect. This is a counter-example
to strict stem-outward ordering within a single word — the ordering
principle holds across the analytical construction (neg aux + main verb)
rather than within a synthetic word.

## References

- Karlsson, F. (2018). *Finnish: A Comprehensive Grammar*. Routledge. Ch. 11.
- Miestamo, M. (2005). *Standard Negation*. Mouton de Gruyter.
- Bybee, J. L. (1985). *Morphology*. Benjamins.
-/

namespace Fragments.Finnish.Negation

open Core.Morphology (MorphCategory MorphRule)

-- ============================================================================
-- § 1: Negative Auxiliary Paradigm
-- ============================================================================

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

-- ============================================================================
-- § 2: Connegative Formation
-- ============================================================================

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
  , isVacuous := false }

/-- The negative auxiliary's agreement rule: semantically vacuous,
    carries person/number agreement that would otherwise be on the main verb. -/
def negAgreementRule (person : Nat) (number : String) : MorphRule Bool :=
  { category := .agreement
  , value := s!"{person}{number}"
  , formRule := fun _ =>
    match person, number with
    | 1, "sg" => "en"  | 2, "sg" => "et"  | 3, "sg" => "ei"
    | 1, "pl" => "emme" | 2, "pl" => "ette" | 3, "pl" => "eivät"
    | _, _ => "ei"
  , featureRule := fun f => { f with person := some (if person == 1 then .first
      else if person == 2 then .second else .third) }
  , semEffect := id
  , isVacuous := true }

-- ============================================================================
-- § 3: Inflection Distribution
-- ============================================================================

/-- Which Bybee categories appear on the negative auxiliary vs. the main verb.

    The negative auxiliary hosts: negation, tense, agreement.
    The main verb retains: stem, aspect (via participle choice). -/
structure InflDistribution where
  onNegAux : List MorphCategory
  onMainVerb : List MorphCategory
  deriving Repr, BEq

/-- Finnish negative construction inflection distribution. -/
def finnishNegDistribution : InflDistribution :=
  { onNegAux := [.negation, .tense, .agreement]
  , onMainVerb := [.stem, .aspect] }

-- ============================================================================
-- § 4: Verification Theorems
-- ============================================================================

/-- The paradigm has exactly 6 forms (3 persons × 2 numbers). -/
theorem paradigm_size : negParadigm.length = 6 := by native_decide

/-- All singular forms are monosyllabic (≤ 2 characters). -/
theorem singular_short :
    (negParadigm.filter (·.number == "sg")).all
      (fun f => f.form.length ≤ 2) = true := by native_decide

/-- All forms share the stem *e-* (first character is 'e'). -/
theorem shared_stem :
    negParadigm.all (fun f => f.form.get ⟨0⟩ == 'e') = true := by
  native_decide

/-- The connegative rule is NOT semantically vacuous — it carries negation. -/
theorem connegative_not_vacuous : connegativeRule.isVacuous = false := rfl

/-- The connegative rule's semantic effect is Boolean negation. -/
theorem connegative_negates : connegativeRule.semEffect true = false := rfl

/-- Agreement on the neg aux IS semantically vacuous. -/
theorem neg_agreement_vacuous : (negAgreementRule 1 "sg").isVacuous = true := rfl

/-- Negation (rank 7) hosts agreement (rank 8) on the negative auxiliary —
    respecting Bybee's hierarchy within the neg aux word. -/
theorem neg_aux_respects_bybee :
    MorphCategory.relevanceRank .negation <
    MorphCategory.relevanceRank .agreement := by decide

end Fragments.Finnish.Negation
