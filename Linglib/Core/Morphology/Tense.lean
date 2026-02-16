import Linglib.Core.Morphology.MorphRule

/-!
# Tense Morphology

Morphological rules for tense marking on verbs.

All rules are `isVacuous := true` because the semantic work (temporal
constraints, Reichenbach frames) lives in the Theory layer
(`Theories/Semantics.Montague/Sentence/Tense/Basic.lean`), not in
the morphological rule itself.

## Synthetic vs Periphrastic

Lakoff (1970) observes that **periphrastic** tense forms (*used to*,
*going to*, *be about to*) cannot express "false" tenses — they require
a literal temporal interpretation. Only **synthetic** forms (*-ed*, *-s*)
can carry the psychological (non-temporal) tense uses. `TenseFormType`
encodes this diagnostic distinction.

## References

- Lakoff, R. (1970). Tense and its relation to participants. *Language* 46(4).
- Bybee, J. L. (1985). Morphology. Benjamins.
-/

namespace Core.Morphology.Tense

/-- Whether a tense form is realized synthetically (inflectional suffix)
    or periphrastically (auxiliary + verb). Lakoff's key diagnostic:
    periphrastic forms block "false" tense interpretations. -/
inductive TenseFormType where
  | synthetic     -- inflectional: *walked*, *walks*
  | periphrastic  -- auxiliary-based: *used to walk*, *going to walk*
  deriving DecidableEq, Repr, BEq

/-- Synthetic past tense rule: appends "-ed" to the lemma.

    Irregular forms (e.g., "went", "was") are supplied via `irregularForm`.
    Semantically vacuous — temporal semantics is handled by `PAST`. -/
def pastRule (σ : Type) (irregularForm : Option String := none) : MorphRule σ :=
  { category := .tense
  , value := "past"
  , formRule := λ lemma_ => irregularForm.getD (lemma_ ++ "ed")
  , featureRule := id
  , semEffect := id
  , isVacuous := true }

/-- Synthetic present tense rule: appends "-s" for 3sg default.

    Semantically vacuous — temporal semantics is handled by `PRES`. -/
def presentRule (σ : Type) (irregularForm : Option String := none) : MorphRule σ :=
  { category := .tense
  , value := "pres"
  , formRule := λ lemma_ => irregularForm.getD (lemma_ ++ "s")
  , featureRule := id
  , semEffect := id
  , isVacuous := true }

/-- Synthetic future marker rule: prepends "will".

    English future is borderline periphrastic, but Lakoff treats bare
    *will* as allowing false-tense interpretations (§5), so we classify
    it as synthetic for the false-tense diagnostic. -/
def futureRule (σ : Type) : MorphRule σ :=
  { category := .tense
  , value := "fut"
  , formRule := λ lemma_ => "will " ++ lemma_
  , featureRule := id
  , semEffect := id
  , isVacuous := true }

/-- Periphrastic past rule: "used to V".

    Cannot express false past (Lakoff §1, ex. 8a). -/
def periphrasticPastRule (σ : Type) : MorphRule σ :=
  { category := .tense
  , value := "past.periph"
  , formRule := λ lemma_ => "used to " ++ lemma_
  , featureRule := id
  , semEffect := id
  , isVacuous := true }

/-- Periphrastic future rule: "going to V".

    Cannot express false future (Lakoff §1). -/
def periphrasticFutureRule (σ : Type) : MorphRule σ :=
  { category := .tense
  , value := "fut.periph"
  , formRule := λ lemma_ => "going to " ++ lemma_
  , featureRule := id
  , semEffect := id
  , isVacuous := true }

/-- Past participle rule: appends "-ed" to the lemma.

    Irregular forms (e.g., "eaten", "slept") are supplied via `irregularForm`.
    Semantically vacuous — participial semantics lives in the Theory layer. -/
def pastPartRule (σ : Type) (irregularForm : Option String := none) : MorphRule σ :=
  { category := .tense
  , value := "pastpart"
  , formRule := λ lemma_ => irregularForm.getD (lemma_ ++ "ed")
  , featureRule := id
  , semEffect := id
  , isVacuous := true }

-- ════════════════════════════════════════════════════
-- § Verification Theorems
-- ════════════════════════════════════════════════════

/-- All tense rules are semantically vacuous. -/
theorem past_vacuous (σ : Type) (irr : Option String) :
    (pastRule σ irr).isVacuous = true := rfl

theorem present_vacuous (σ : Type) (irr : Option String) :
    (presentRule σ irr).isVacuous = true := rfl

theorem future_vacuous (σ : Type) :
    (futureRule σ).isVacuous = true := rfl

theorem periphrasticPast_vacuous (σ : Type) :
    (periphrasticPastRule σ).isVacuous = true := rfl

theorem periphrasticFuture_vacuous (σ : Type) :
    (periphrasticFutureRule σ).isVacuous = true := rfl

theorem pastPart_vacuous (σ : Type) (irr : Option String) :
    (pastPartRule σ irr).isVacuous = true := rfl

/-- All tense rules have category `.tense`. -/
theorem past_category (σ : Type) (irr : Option String) :
    (pastRule σ irr).category = .tense := rfl

theorem present_category (σ : Type) (irr : Option String) :
    (presentRule σ irr).category = .tense := rfl

theorem future_category (σ : Type) :
    (futureRule σ).category = .tense := rfl

theorem periphrasticPast_category (σ : Type) :
    (periphrasticPastRule σ).category = .tense := rfl

theorem periphrasticFuture_category (σ : Type) :
    (periphrasticFutureRule σ).category = .tense := rfl

theorem pastPart_category (σ : Type) (irr : Option String) :
    (pastPartRule σ irr).category = .tense := rfl

end Core.Morphology.Tense
