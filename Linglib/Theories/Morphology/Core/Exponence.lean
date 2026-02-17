import Linglib.Core.MorphRule

/-!
# Morphological Exponence Rules

Concrete instantiations of `MorphRule` for functional categories.

All rules that are purely formal (no semantic contribution) have
`isVacuous := true`. Number marking on nouns is the exception:
singular restricts to atoms, plural applies algebraic closure (Link 1983).

## References

- Bybee, J. L. (1985). Morphology. Benjamins.
- Comrie, B. (1976). Aspect. Cambridge University Press.
- Kennedy, C. (2007). Vagueness and grammar.
- Lakoff, R. (1970). Tense and its relation to participants. *Language* 46(4).
- Link, G. (1983). The logical analysis of plurals and mass terms.
-/

-- ════════════════════════════════════════════════════
-- § Tense
-- ════════════════════════════════════════════════════

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

-- ════════════════════════════════════════════════════
-- § Aspect
-- ════════════════════════════════════════════════════

namespace Core.Morphology.Aspect

/-- Present participle rule: appends "-ing" to the lemma.

    Irregular forms (e.g., "running", "lying") are supplied via `irregularForm`.
    Semantically vacuous — progressive/gerundive semantics is handled in Theory. -/
def presPartRule (σ : Type) (irregularForm : Option String := none) : MorphRule σ :=
  { category := .aspect
  , value := "prespart"
  , formRule := λ lemma_ => irregularForm.getD (lemma_ ++ "ing")
  , featureRule := id
  , semEffect := id
  , isVacuous := true }

theorem presPart_vacuous (σ : Type) (irr : Option String) :
    (presPartRule σ irr).isVacuous = true := rfl

theorem presPart_category (σ : Type) (irr : Option String) :
    (presPartRule σ irr).category = .aspect := rfl

end Core.Morphology.Aspect

-- ════════════════════════════════════════════════════
-- § Number
-- ════════════════════════════════════════════════════

namespace Core.Morphology.Number

/-- Singular rule for nouns: adds atomicity condition.

    Semantics: `pred ↦ (λ x => pred x ∧ Atom x)`
    This implements Link (1983): singular nouns denote atomic individuals. -/
def singularNounRule {α : Type} (atomPred : α → Bool) :
    MorphRule (α → Bool) :=
  { category := .number
  , value := "sg"
  , formRule := id
  , featureRule := λ f => { f with number := some .Sing }
  , semEffect := λ pred x => pred x && atomPred x }

/-- Plural rule for nouns (regular: append -s).

    Semantics: `pred ↦ closurePred pred ∧ ¬Atom`
    where `closurePred` is Link's algebraic closure (from `Core/Mereology.lean`).

    This makes "dogs" true of plural individuals (sums of dogs). -/
def pluralNounRule {α : Type}
    (closurePred : (α → Bool) → α → Bool)
    (atomPred : α → Bool)
    (irregularForm : Option String := none) :
    MorphRule (α → Bool) :=
  { category := .number
  , value := "pl"
  , formRule := λ lemma_ => irregularForm.getD (lemma_ ++ "s")
  , featureRule := λ f => { f with number := some .Plur }
  , semEffect := λ pred x => closurePred pred x && !atomPred x }

/-- Plural rule with identity semantics, for models without mereological
    structure (e.g., toy models with only atomic individuals). -/
def pluralNounRuleFlat {α : Type}
    (irregularForm : Option String := none) :
    MorphRule (α → Bool) :=
  { category := .number
  , value := "pl"
  , formRule := λ lemma_ => irregularForm.getD (lemma_ ++ "s")
  , featureRule := λ f => { f with number := some .Plur }
  , semEffect := id
  , isVacuous := true }

/-- Verb agreement -s: formal change only, semantically vacuous. -/
def verbAgreement3sg (σ : Type) : MorphRule σ :=
  { category := .agreement
  , value := "3sg"
  , formRule := λ lemma_ => lemma_ ++ "s"
  , featureRule := λ f => { f with number := some .Sing, person := some .third }
  , semEffect := id
  , isVacuous := true }

/-- Verb agreement is semantically vacuous. -/
theorem verbAgreement_preserves_meaning (σ : Type) (meaning : σ) :
    (verbAgreement3sg σ).semEffect meaning = meaning := rfl

end Core.Morphology.Number

-- ════════════════════════════════════════════════════
-- § Degree
-- ════════════════════════════════════════════════════

namespace Core.Morphology.Degree

/-- Comparative degree rule: generates the comparative form of an adjective.

    Regular formation appends "-er" to the lemma; irregular forms
    (e.g., "better", "more expensive") are supplied via `irregularForm`.

    Semantically vacuous at the morphological level — comparative
    semantics (degree quantification) is handled compositionally
    by `Semantics.Lexical.Adjective.Comparative`. -/
def comparativeRule (σ : Type) (irregularForm : Option String := none) : MorphRule σ :=
  { category := .degree
  , value := "comp"
  , formRule := λ lemma_ => irregularForm.getD (lemma_ ++ "er")
  , featureRule := id
  , semEffect := id
  , isVacuous := true }

/-- Superlative degree rule: generates the superlative form of an adjective.

    Regular formation appends "-est" to the lemma; irregular forms
    (e.g., "best", "most expensive") are supplied via `irregularForm`.

    Semantically vacuous at the morphological level — superlative
    semantics (MAX operator) is handled compositionally. -/
def superlativeRule (σ : Type) (irregularForm : Option String := none) : MorphRule σ :=
  { category := .degree
  , value := "super"
  , formRule := λ lemma_ => irregularForm.getD (lemma_ ++ "est")
  , featureRule := id
  , semEffect := id
  , isVacuous := true }

/-- Both degree rules are semantically vacuous. -/
theorem comparative_vacuous (σ : Type) (irr : Option String) :
    (comparativeRule σ irr).isVacuous = true := rfl

theorem superlative_vacuous (σ : Type) (irr : Option String) :
    (superlativeRule σ irr).isVacuous = true := rfl

/-- Both degree rules have category `.degree`. -/
theorem comparative_category (σ : Type) (irr : Option String) :
    (comparativeRule σ irr).category = .degree := rfl

theorem superlative_category (σ : Type) (irr : Option String) :
    (superlativeRule σ irr).category = .degree := rfl

end Core.Morphology.Degree
