import Linglib.Fragments.Dutch.Gender
import Linglib.Syntax.Category.Determiner.Basic

/-!
# Dutch determiners

The Dutch articles and demonstratives after Broekhuis and den Dikken's grammar. The definite
article is *de* with common-gender singulars and every plural and *het* with neuter singulars,
one syncretic definite over the [schwarz-2009] use types; the indefinite article *een* occurs
with singular count nouns only, the indefinite plural and mass noun phrases being bare; the
negative article *geen* occurs with all three. The proximate demonstrative *deze* ~ *dit* and
the distal *die* ~ *dat* agree exactly as the definite article does. The three agreeing
determiners are the agreement evidence for the two-gender carrier of `Dutch.Gender`.

## Main declarations

* `Dutch.Determiners.Target` and `Dutch.Determiners.singular`: the determiners whose singular
  form agrees in gender, and that form; `Dutch.Determiners.plural` is the common-gender form,
  which every plural takes.
* `Dutch.Determiners.injective_singular` and `Dutch.Determiners.faithful`: each agreeing
  determiner distinguishes the two genders, so the carrier is faithful to the evidence.
* `Dutch.Determiners.inventory` and `Dutch.Determiners.marking`: the inventory, whose citation
  forms are the plural forms, and its derived [moroney-2021] cell.

## References

* [broekhuis-dendikken-2012]
* [schwarz-2009]
* [moroney-2021]
-/

namespace Dutch.Determiners

/-! ### Gender agreement -/

/-- The determiners whose singular form agrees in gender: the definite article and the
proximate and distal demonstratives. -/
inductive Target where
  | definite
  | proximate
  | distal
  deriving DecidableEq, Repr, Fintype

/-- The singular form of each agreeing determiner by gender: *de*, *deze* and *die* with
common-gender nouns, *het*, *dit* and *dat* with neuter nouns. -/
def singular : Gender.Value → Target → String
  | .common, .definite => "de"
  | .common, .proximate => "deze"
  | .common, .distal => "die"
  | .neuter, .definite => "het"
  | .neuter, .proximate => "dit"
  | .neuter, .distal => "dat"

/-- The plural form of each agreeing determiner, which is its common-gender singular form. -/
def plural (t : Target) : String := singular .common t

/-- Each agreeing determiner distinguishes the two genders in the singular. -/
theorem injective_singular : ∀ t, Function.Injective (singular · t) := by decide

/-- The two-gender carrier is faithful to the determiner evidence. -/
theorem faithful : Gender.Faithful singular :=
  fun _ _ h ↦ injective_singular .definite (congrFun h _)

/-! ### The inventory -/

/-- The definite article *de* ~ *het*, one syncretic definite over the [schwarz-2009] use
types. -/
def de : Article :=
  { form := plural .definite, definiteness := .definite, exponent := .dedicatedMorpheme
    uses := [.immediateSituation, .largerSituation, .anaphoric, .donkey] }

/-- The indefinite article *een*, of singular count nouns; the indefinite plural and mass noun
phrases are bare. -/
def een : Article := { form := "een", definiteness := .indefinite, exponent := .dedicatedMorpheme }

/-- The negative article *geen*, of singular, plural and mass nouns alike. -/
def geen : Quantifier := { form := "geen", selectsMass := true }

/-- The proximate demonstrative *deze* ~ *dit*. -/
def deze : DemonstrativeDeterminer := { form := plural .proximate, deictic := .proximal }

/-- The distal demonstrative *die* ~ *dat*. -/
def die : DemonstrativeDeterminer := { form := plural .distal, deictic := .distal }

/-- The Dutch determiner inventory. -/
def inventory : Determiner.Inventory :=
  [.article de, .article een, .quantifier geen, .demonstrative deze, .demonstrative die]

/-- Dutch derives the `.generallyMarked` [moroney-2021] cell. -/
theorem marking : inventory.markingStrategy = .generallyMarked := by decide

end Dutch.Determiners
