import Linglib.Core.MorphRule

/-!
# Number Morphology

Concrete morphological rules for number marking on nouns and verb agreement.

Noun number is semantically non-trivial: singular restricts to atoms,
plural applies algebraic closure and excludes atoms (Link 1983). Verb
agreement is semantically vacuous (`semEffect := id`).

The rules are parameterized over `atomPred` and `closurePred` so they
work with any domain that has mereological structure (see `Core/Mereology.lean`
for the algebraic definitions).

## References

- Link, G. (1983). The logical analysis of plurals and mass terms.
- Champollion, L. (2017). Parts of a Whole. OUP.
-/

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
