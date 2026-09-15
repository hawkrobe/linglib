import Linglib.Syntax.Category.Determiner.Basic

/-!
# Dutch determiners

The Dutch articles: the definite *de* of common-gender and plural nouns and *het* of neuter
singulars, one syncretic definite covering the [schwarz-2009] use types, and the indefinite
singular *een*.

## References

* [schwarz-2009]
-/

namespace Dutch.Determiners

/-- *de* — the definite article of common-gender and plural nouns. -/
def de : Article :=
  { form := "de", definiteness := .definite, exponent := .dedicatedMorpheme
    uses := [.immediateSituation, .largerSituation, .anaphoric, .donkey] }

/-- *het* — the definite article of neuter singulars. -/
def het : Article :=
  { form := "het", definiteness := .definite, exponent := .dedicatedMorpheme
    uses := [.immediateSituation, .largerSituation, .anaphoric, .donkey] }

/-- *een* — the indefinite article. -/
def een : Article := { form := "een", definiteness := .indefinite, exponent := .dedicatedMorpheme }

/-- The Dutch determiner inventory. -/
def inventory : Determiner.Inventory := [.article de, .article het, .article een]

/-- Dutch derives the `.generallyMarked` [moroney-2021] cell. -/
theorem marking : inventory.markingStrategy = .generallyMarked := by decide

end Dutch.Determiners
