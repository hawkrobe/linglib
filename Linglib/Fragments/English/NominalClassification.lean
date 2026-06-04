import Linglib.Core.Word
import Linglib.Features.CoreferenceStatus
import Linglib.Syntax.Pronoun.Capabilities
import Linglib.Fragments.English.Pronouns

/-!
# English nominal classification for binding

Lexicon-driven classification of English nominals into `Features.BindingClass` — the
binding-class **source** the coreference/binding analyses in every syntactic framework
(`Syntax.Minimalist.Coreference`, `Syntax.HPSG.Coreference`, `Syntax.DependencyGrammar`)
consume. The class is read from each lexicon entry's declared `Pronoun.bindingClass` (set at
the entry; see `English.Pronouns`), looked up by surface form — one `Features.BindingSource
Word`. Other theories may source the class differently (HPSG sorts, minimal-pronoun context);
the engine is polymorphic over the source.

φ-feature agreement is *not* here: it is `Word.Agree` (`Core.Word`), a feature-based relation
over `UD.MorphFeatures.compatible`.

## Main definitions

* `classifyNominal` — the English `Features.BindingSource Word`: the binding class each
  matching lexicon entry *declares*, with a UPOS fallback for R-expressions.
-/

namespace English.NominalClassification

open Features (BindingClass BindingSource)

/-- Is this a nominal category (proper noun, common noun, or pronoun)? -/
def isNominalCat (c : UD.UPOS) : Bool :=
  c == .PROPN || c == .NOUN || c == .PRON

/-- The full English pro-form lexicon; each entry carries its declared `bindingClass`
(set at the entry defs in `English.Pronouns`). -/
def lexicon : List Pronoun :=
  English.Pronouns.reflexives ++ English.Pronouns.reciprocals ++ English.Pronouns.whWords
    ++ English.pronouns.map (·.toPronoun)

/-- Classify an English nominal: the binding class the matching lexicon entry *declares*
(`Pronoun.bindingClass`), looked up by surface form, with a UPOS R-expression fallback. The
binding class is sourced from the entry's own declaration, not from list membership. -/
def classifyNominal : BindingSource Word := fun w =>
  match lexicon.find? (·.form == w.form) with
  | some e => e.bindingClass
  | none => if isNominalCat w.cat then some .rExpression else none

/-- Every reflexive entry is a Principle-A anaphor by its declaration — `Bound.IsAnaphor`
(over `bindingClass`) holds across the `reflexives` lexicon. -/
theorem reflexives_are_anaphors : ∀ p ∈ English.Pronouns.reflexives, Bound.IsAnaphor p := by decide

end English.NominalClassification
