import Linglib.Core.Word
import Linglib.Features.CoreferenceStatus
import Linglib.Fragments.English.Pronouns

/-!
# English nominal classification for binding

Lexicon-driven classification of English nominals into `Features.NominalType`,
plus φ-feature agreement, shared by the coreference/binding analyses in every
syntactic framework (`Syntax.Minimalist.Coreference`, `Syntax.HPSG.Coreference`,
`Syntax.DependencyGrammar`). Each previously re-stipulated these with hardcoded
pronoun-form string lists; routing through `English.Pronouns` makes
the three frameworks classify against one lexicon.

## Main definitions

* `classifyNominal` — `Word → Option Features.NominalType`, via the English
  pronoun lexicon lists (`reflexives`/`reciprocals`/personal/`whWords`) with a
  UPOS fallback for R-expressions.
* `phiAgree` — person/number/gender agreement between two nominals, as a `Prop`
  with a `Decidable` instance.
-/

namespace English.NominalClassification

open Features (NominalType)

/-- Is this a nominal category (proper noun, common noun, or pronoun)? -/
def isNominalCat (c : UD.UPOS) : Bool :=
  c == .PROPN || c == .NOUN || c == .PRON

/-- Classify a word as a binding-theoretic nominal type.

    Derives the classification from the English pronoun lexicon lists rather
    than a per-entry tag: a form in `reflexives` or `reciprocals` is an anaphor,
    a form in the personal or wh lists is a pronoun, and any other nominal
    category is an R-expression. -/
def classifyNominal (w : Word) : Option NominalType :=
  if English.Pronouns.reflexives.any (·.form == w.form) then some .reflexive
  else if English.Pronouns.reciprocals.any (·.form == w.form) then some .reciprocal
  else if English.pronouns.any (·.form == w.form)
        || English.Pronouns.whWords.any (·.form == w.form) then some .pronoun
  else if isNominalCat w.cat then some .rExpression
  else none

/-- φ-feature agreement (person, number, gender) between two nominals.
    Person and number compare the morphosyntactic features directly; gender
    routes through the Fragment's `genderAgrees` (unspecified gender agrees
    with anything). -/
def phiAgree (w1 w2 : Word) : Prop :=
  (match w1.features.person, w2.features.person with
    | some p1, some p2 => p1 = p2
    | _, _ => True) ∧
  (match w1.features.number, w2.features.number with
    | some n1, some n2 => n1 = n2
    | _, _ => True) ∧
  English.Pronouns.genderAgrees w1.form w2.form = true

instance (w1 w2 : Word) : Decidable (phiAgree w1 w2) := by
  unfold phiAgree
  have d1 : Decidable
      (match w1.features.person, w2.features.person with
       | some p1, some p2 => p1 = p2
       | _, _ => True) := by
    split <;> infer_instance
  have d2 : Decidable
      (match w1.features.number, w2.features.number with
       | some n1, some n2 => n1 = n2
       | _, _ => True) := by
    split <;> infer_instance
  exact inferInstance

end English.NominalClassification
