import Linglib.Core.Word
import Linglib.Features.CoreferenceStatus
import Linglib.Fragments.English.Pronouns

/-!
# English nominal classification for binding

Lexicon-driven classification of English nominals into `Features.BindingClass`,
shared by the coreference/binding analyses in every syntactic framework
(`Syntax.Minimalist.Coreference`, `Syntax.HPSG.Coreference`,
`Syntax.DependencyGrammar`). Each previously re-stipulated this with hardcoded
pronoun-form string lists; routing through `English.Pronouns` makes
the three frameworks classify against one lexicon.

φ-feature agreement is *not* here: it is `Word.Agree` (`Core.Word`), a
feature-based relation over `UD.MorphFeatures.compatible` that reads the
gender carried by `toWord` — no surface-form gender table.

## Main definitions

* `classifyNominal` — `Word → Option Features.BindingClass`, via the English
  pronoun lexicon lists (`reflexives`/`reciprocals`/personal/`whWords`) with a
  UPOS fallback for R-expressions.
-/

namespace English.NominalClassification

open Features (BindingClass)

/-- Is this a nominal category (proper noun, common noun, or pronoun)? -/
def isNominalCat (c : UD.UPOS) : Bool :=
  c == .PROPN || c == .NOUN || c == .PRON

/-- Classify a word as a binding-theoretic nominal type.

    Derives the classification from the English pronoun lexicon lists rather
    than a per-entry tag: a form in `reflexives` or `reciprocals` is an anaphor,
    a form in the personal or wh lists is a pronoun, and any other nominal
    category is an R-expression. -/
def classifyNominal (w : Word) : Option BindingClass :=
  if English.Pronouns.reflexives.any (·.form == w.form) then some .reflexive
  else if English.Pronouns.reciprocals.any (·.form == w.form) then some .reciprocal
  else if English.pronouns.any (·.form == w.form)
        || English.Pronouns.whWords.any (·.form == w.form) then some .pronoun
  else if isNominalCat w.cat then some .rExpression
  else none

end English.NominalClassification
